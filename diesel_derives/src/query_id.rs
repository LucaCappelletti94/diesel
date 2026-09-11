use diesel_attribute_parser::{StructAttr, parse_attributes};
use proc_macro2::TokenStream;
use quote::quote;
use syn::DeriveInput;
use syn::Result;
use syn::parse_quote;

use crate::util::CratePath;

pub fn derive(mut item: DeriveInput) -> Result<TokenStream> {
    let mut crate_path = None;
    let mut is_window_function = false;
    for attr in parse_attributes(&item.attrs)? {
        match attr.item {
            StructAttr::CratePath(_, path) => crate_path = Some(path),
            StructAttr::InternalIsWindow(_, value) => is_window_function = value.value(),
            _ => {}
        }
    }

    for ty_param in item.generics.type_params_mut() {
        ty_param
            .bounds
            .push(parse_quote!(diesel::query_builder::QueryId));
    }
    let (impl_generics, ty_generics, where_clause) = item.generics.split_for_impl();

    let struct_name = &item.ident;
    // Arguments must follow the declaration order of the parameters, so walk them in
    // order rather than grouping by kind. Lifetimes become `'static`, which is both
    // required (`Any` implies `'static`) and correct (a lifetime cannot change the SQL).
    let query_id_args = item.generics.params.iter().map(|param| match param {
        syn::GenericParam::Lifetime(_) => quote!('static),
        syn::GenericParam::Type(ty_param) => {
            let ident = &ty_param.ident;
            quote!(<#ident as diesel::query_builder::QueryId>::QueryId)
        }
        syn::GenericParam::Const(const_param) => {
            let ident = &const_param.ident;
            quote!(#ident)
        }
    });

    let ty_params = item
        .generics
        .type_params()
        .map(|ty_param| &ty_param.ident)
        .collect::<Vec<_>>();

    let has_static_query_id = ty_params
        .iter()
        .map(|ty_param| quote!(<#ty_param as diesel::query_builder::QueryId>::HAS_STATIC_QUERY_ID));
    let is_window_function_list = ty_params
        .iter()
        .map(|ty_param| quote!(<#ty_param as diesel::query_builder::QueryId>::IS_WINDOW_FUNCTION));
    let is_window_function = if is_window_function {
        quote! { true }
    } else {
        quote! { #(#is_window_function_list ||)* false }
    };

    let crate_path = CratePath::new(crate_path.as_ref());
    Ok(crate_path.wrap_in_dummy_mod(quote! {
        #[allow(non_camel_case_types)]
        impl #impl_generics diesel::query_builder::QueryId for #struct_name #ty_generics
        #where_clause
        {
            type QueryId = #struct_name<#(#query_id_args,)*>;

            const HAS_STATIC_QUERY_ID: bool = #(#has_static_query_id &&)* true;

            const IS_WINDOW_FUNCTION: bool = #is_window_function;
        }
    }))
}
