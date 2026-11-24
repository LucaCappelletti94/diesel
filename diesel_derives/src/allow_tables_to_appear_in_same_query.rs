use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{Path, Token};

struct AllowTablesToAppearInSameQuery {
    tables: Punctuated<Path, Token![,]>,
    external_tables: Option<Punctuated<Path, Token![,]>>,
}

impl Parse for AllowTablesToAppearInSameQuery {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut tables = Punctuated::new();
        while !input.is_empty() && !input.peek(Token![;]) {
            tables.push_value(input.parse()?);
            if input.is_empty() || input.peek(Token![;]) {
                break;
            }
            tables.push_punct(input.parse()?);
        }
        let external_tables = if input.peek(Token![;]) {
            input.parse::<Token![;]>()?;
            Some(input.parse_terminated(Path::parse, Token![,])?)
        } else {
            None
        };
        Ok(AllowTablesToAppearInSameQuery {
            tables,
            external_tables,
        })
    }
}

pub fn expand(input: TokenStream) -> TokenStream {
    let input: AllowTablesToAppearInSameQuery = match syn::parse2(input) {
        Ok(input) => input,
        Err(e) => return e.to_compile_error(),
    };

    let tables: Vec<Path> = input.tables.into_iter().collect();
    let external_tables = input
        .external_tables
        .map(|tables| tables.into_iter().collect::<Vec<_>>());
    let pair_count = external_tables.as_ref().map_or_else(
        || tables.len() * tables.len().saturating_sub(1),
        |external_tables| 2 * tables.len() * external_tables.len(),
    );
    let mut left_impls = Vec::with_capacity(pair_count);
    let mut right_impls = Vec::with_capacity(pair_count);

    for (index, left) in tables.iter().enumerate() {
        let right_tables = external_tables.as_deref().unwrap_or(&tables[index + 1..]);
        for right in right_tables {
            left_impls.push(left);
            right_impls.push(right);
            left_impls.push(right);
            right_impls.push(left);
        }
    }

    quote! {
        #(
            impl ::diesel::query_source::TableNotEqual<#right_impls::table> for #left_impls::table {}
        )*
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semicolon_pairs_only_opposite_lists() {
        let expanded = expand(quote!(users, posts; external::first, external::second));
        let expected = quote! {
            impl ::diesel::query_source::TableNotEqual<external::first::table> for users::table {}
            impl ::diesel::query_source::TableNotEqual<users::table> for external::first::table {}
            impl ::diesel::query_source::TableNotEqual<external::second::table> for users::table {}
            impl ::diesel::query_source::TableNotEqual<users::table> for external::second::table {}
            impl ::diesel::query_source::TableNotEqual<external::first::table> for posts::table {}
            impl ::diesel::query_source::TableNotEqual<posts::table> for external::first::table {}
            impl ::diesel::query_source::TableNotEqual<external::second::table> for posts::table {}
            impl ::diesel::query_source::TableNotEqual<posts::table> for external::second::table {}
        };
        assert_eq!(expanded.to_string(), expected.to_string());
    }

    #[test]
    fn semicolon_accepts_trailing_commas() {
        assert_eq!(
            expand(quote!(users,; external::first,)).to_string(),
            expand(quote!(users; external::first)).to_string(),
        );
    }

    #[test]
    fn semicolon_empty_lists_add_no_pairs() {
        assert!(expand(quote!(users;)).is_empty());
        assert!(expand(quote!(; external::first)).is_empty());
        assert!(expand(quote!(;)).is_empty());
    }
}
