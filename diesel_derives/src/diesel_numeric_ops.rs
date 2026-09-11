use diesel_attribute_parser::{StructAttr, parse_attributes};
use proc_macro2::TokenStream;
use quote::quote;
use syn::DeriveInput;
use syn::Result;
use syn::parse_quote;

use crate::util::CratePath;

pub fn derive(mut item: DeriveInput) -> Result<TokenStream> {
    let crate_path = parse_attributes(&item.attrs)?
        .into_iter()
        .find_map(|attr| match attr.item {
            StructAttr::CratePath(_, path) => Some(path),
            _ => None,
        });

    let struct_name = &item.ident;

    {
        let where_clause = item
            .generics
            .where_clause
            .get_or_insert(parse_quote!(where));
        where_clause.predicates.push(parse_quote!(Self: Expression));
        where_clause.predicates.push_punct(Default::default());
    }

    let (_, ty_generics, where_clause) = item.generics.split_for_impl();
    let mut impl_generics = item.generics.clone();
    impl_generics.params.push(parse_quote!(__Rhs));
    let (impl_generics, _, _) = impl_generics.split_for_impl();

    let crate_path = CratePath::new(crate_path.as_ref());
    Ok(crate_path.wrap_in_dummy_mod(quote! {
        use diesel::internal::derives::numeric_ops as ops;
        use diesel::expression::{Expression, AsExpression};
        use diesel::sql_types::ops::{Add, Sub, Mul, Div};
        use diesel::sql_types::{SqlType, SingleValue};

        impl #impl_generics ::core::ops::Add<__Rhs> for #struct_name #ty_generics
        #where_clause
            Self: Expression,
            <Self as Expression>::SqlType: Add,
            <<Self as Expression>::SqlType as Add>::Rhs: SqlType + SingleValue,
            __Rhs: AsExpression<<<Self as Expression>::SqlType as Add>::Rhs>,
        {
            type Output = ops::Add<Self, __Rhs::Expression>;

            fn add(self, rhs: __Rhs) -> Self::Output {
                ops::Add::new(self, rhs.as_expression())
            }
        }

        impl #impl_generics ::core::ops::Sub<__Rhs> for #struct_name #ty_generics
        #where_clause
            Self: Expression,
            <Self as Expression>::SqlType: Sub,
            <<Self as Expression>::SqlType as Sub>::Rhs: SqlType + SingleValue,
            __Rhs: AsExpression<<<Self as Expression>::SqlType as Sub>::Rhs>,
        {
            type Output = ops::Sub<Self, __Rhs::Expression>;

            fn sub(self, rhs: __Rhs) -> Self::Output {
                ops::Sub::new(self, rhs.as_expression())
            }
        }

        impl #impl_generics ::core::ops::Mul<__Rhs> for #struct_name #ty_generics
        #where_clause
            Self: Expression,
            <Self as Expression>::SqlType: Mul,
            <<Self as Expression>::SqlType as Mul>::Rhs: SqlType + SingleValue,
            __Rhs: AsExpression<<<Self as Expression>::SqlType as Mul>::Rhs>,
        {
            type Output = ops::Mul<Self, __Rhs::Expression>;

            fn mul(self, rhs: __Rhs) -> Self::Output {
                ops::Mul::new(self, rhs.as_expression())
            }
        }

        impl #impl_generics ::core::ops::Div<__Rhs> for #struct_name #ty_generics
        #where_clause
            Self: Expression,
            <Self as Expression>::SqlType: Div,
            <<Self as Expression>::SqlType as Div>::Rhs: SqlType + SingleValue,
            __Rhs: AsExpression<<<Self as Expression>::SqlType as Div>::Rhs>,
        {
            type Output = ops::Div<Self, __Rhs::Expression>;

            fn div(self, rhs: __Rhs) -> Self::Output {
                ops::Div::new(self, rhs.as_expression())
            }
        }
    }))
}
