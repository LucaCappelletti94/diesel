use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{DeriveInput, Ident, Index, Result, parse_quote};

use crate::field::Field;
use crate::model::Model;
use crate::util::wrap_in_dummy_mod;

pub fn derive(item: DeriveInput) -> Result<TokenStream> {
    let model = Model::from_item(&item, false, true)?;

    let struct_name = &item.ident;
    let field_ty = &model
        .fields()
        .iter()
        .map(Field::ty_for_deserialize)
        .collect::<Vec<_>>();
    let build_expr = model.fields().iter().enumerate().map(|(i, f)| {
        let field_name = &f.name;
        let i = Index::from(i);
        // we explicitly call `.try_into()` here
        // instead of using the fully qualified variant
        // to allow also using a `.try_into()` method on the type
        // itself without going through the trait
        quote!(#field_name: row.#i.try_into()?)
    });
    let st_idents: Vec<Ident> = (0..model.fields().len())
        .map(|i| Ident::new(&format!("__ST{i}"), Span::mixed_site()))
        .collect();
    let sql_type = st_idents.iter().map(|i| quote!(#i)).collect::<Vec<_>>();
    let sql_type = &sql_type;

    let mut generics = item.generics;
    let ty_generics = {
        let (_, tg, _) = generics.split_for_impl();
        quote!(#tg)
    };
    generics
        .params
        .push(parse_quote!(__DB: diesel::backend::Backend));
    for ident in &st_idents {
        generics.params.push(parse_quote!(#ident));
    }
    {
        let where_clause = generics
            .where_clause
            .get_or_insert_with(|| parse_quote!(where));
        where_clause
            .predicates
            .push(parse_quote!((#(#field_ty,)*): diesel::deserialize::FromStaticSqlRow<(#(#sql_type,)*), __DB>));
    }
    let (impl_generics, _, where_clause) = generics.split_for_impl();

    Ok(wrap_in_dummy_mod(quote! {
        use diesel::row::{Row as _, Field as _};

        impl #impl_generics diesel::deserialize::Queryable<(#(#sql_type,)*), __DB> for #struct_name #ty_generics
            #where_clause
        {
            type Row = (#(#field_ty,)*);

            fn build(row: (#(#field_ty,)*)) -> diesel::deserialize::Result<Self> {
                use std::convert::TryInto;
                diesel::deserialize::Result::Ok(Self {
                    #(#build_expr,)*
                })
            }
        }
    }))
}
