/*
 *
 *
 * Copyright 2024 Michał Margos
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

extern crate proc_macro;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};

use syn::{parse_macro_input, DeriveInput, Data, DataStruct, Meta, MetaList, braced, Token, Error, token, Generics, Path, Signature, AngleBracketedGenericArguments, FnArg, Attribute, Fields, DataEnum, Expr};
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::token::Question;

struct FuncImpl {
    sig: Signature,
    details: Details
}

impl Parse for FuncImpl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            sig: input.parse()?,
            details: input.parse()?
        })
    }
}

fn merge_partials<I: Iterator<Item = TokenStream2>>(mut partials: I, details: &Details) -> syn::Result<TokenStream2> {
    Ok(match &details.aggregate {
        Some(Aggregate::NoConstruct(aggregate)) => {
            partials.reduce(|x, y| aggregate.aggregate(x, y)).unwrap()
        }
        None => {
            partials.next().unwrap()
        }
        _ => unreachable!()
    })
}

impl FuncImpl {
    /// If has a receiver, requires destructurization,
    /// If aggregated with construct, requires self-type
    fn derive_fields(
        &self,
        fields: &Fields,
        trait_path: &Path,
        question: &Option<Question>
    ) -> syn::Result<TokenStream2> {
        let partials = match &self.details.marker {
            Some(v) => {
                let mut partials = Vec::new();

                for (i, f) in fields.iter().enumerate() {
                    if verify_marker(&f.attrs, v)? {
                        partials.push((i, f));
                    }
                }

                partials
            },
            None => fields.iter().enumerate().collect()
        }.into_iter();

        let (has_receiver, arg_count) = if self.sig.receiver().is_some() {
            (true, self.sig.inputs.len() - 1)
        } else {
            (false, self.sig.inputs.len())
        };

        let fn_ident = &self.sig.ident;
        let variadic = &self.sig.variadic;

        let mut partials2 = Vec::new();
        for (i, f) in partials {
            let arg2 = (0..).take(arg_count).map(|x| format_ident!("arg{x}"));
            let ty = &f.ty;
            let recv = if has_receiver {
                let v_it = format_ident!("f{i}");
                quote! { #v_it, }
            } else {
                quote! {}
            };

            let func_def = quote! { <#ty as #trait_path> :: #fn_ident };
            let func = if let Some(marker) = self.details.override_marker.as_ref() {
                if let Some(func) = verify_override(&f.attrs, marker)? {
                    quote! { (#func) }
                } else {
                    func_def
                }
            } else {
                func_def
            };

            partials2.push(quote! {
                #func (#recv #(#arg2,)* #variadic) #question
            });
        }
        let partials = partials2;

        // Include init param
        let partials = self.details.init.as_ref().into_iter().map(|x| quote! {(#x)}).chain(partials);

        Ok(if self.details.aggregate == Some(Aggregate::Construct) {
            match fields {
                Fields::Named(named) => {
                    let field = named.named.iter().map(|x| &x.ident);

                    quote! {
                        {
                            #(#field: #partials),*
                        }
                    }
                }
                Fields::Unnamed(_) => {
                    quote! {
                        (#(#partials),*)
                    }
                }
                Fields::Unit => quote! {}
            }
        } else {
            merge_partials(partials, &self.details)?
        })
    }

    fn derive_struct(mut self, trait_path: &Path, data: &DataStruct) -> syn::Result<TokenStream2> {
        let where_clause = self.sig.generics.where_clause.take();
        let question = self.details.wrap.is_some().then_some(Token!(?)(Span::call_site()));

        if self.details.variant_aggregate.is_some() || self.details.variant_marker.is_some() || self.details.variant_init.is_some() {
            return Err(Error::new(self.details.span, "variant-related parameters are not allowed on struct impls"));
        }

        let Signature {
            constness,
            asyncness,
            unsafety,
            abi,
            ident,
            generics,
            inputs,
            variadic,
            output,
            ..
        } = &self.sig;

        let arg1 = (0..).map(|i| format_ident!("arg{i}"));

        let ty = inputs.iter().flat_map(|x| match x {
            FnArg::Receiver(_) => None,
            FnArg::Typed(t) => Some(&t.ty)
        });
        let recv = self.sig.receiver();

        let field_code = self.derive_fields(&data.fields, trait_path, &question)?;

        let self_type = (self.details.aggregate == Some(Aggregate::Construct)).then_some(quote! {Self});

        let destructurization = if recv.is_some() {
            let field_var = (0..data.fields.len()).map(|i| format_ident!("f{i}"));

            match &data.fields {
                Fields::Named(named) => {
                    let field_name = named.named.iter().map(|f| &f.ident);

                    quote! {
                        let Self {
                            #(#field_name: #field_var),*
                        } = self;
                    }
                }
                Fields::Unnamed(_) => {
                    quote! {
                        let Self(#(#field_var)*) = self;
                    }
                }
                Fields::Unit => quote!{}
            }
        } else {
            quote! {}
        };

        let code = quote! {
            #destructurization

            #self_type #field_code
        };

        let code = wrap(&self.details.wrap, code);

        let recv = recv.map(|x| quote! {#x,});

        Ok(quote! {
            #constness #asyncness #unsafety #abi fn #ident #generics(#recv #(#arg1: #ty,)* #variadic) #output #where_clause {
                #code
            }
        })
    }

    fn derive_enum(mut self, trait_path: &Path, data: &DataEnum) -> syn::Result<TokenStream2> {
        let where_clause = self.sig.generics.where_clause.take();
        let question = self.details.wrap.is_some().then_some(Token!(?)(Span::call_site()));

        let Signature {
            constness,
            asyncness,
            unsafety,
            abi,
            ident,
            generics,
            inputs,
            variadic,
            output,
            ..
        } = &self.sig;

        let arg_count = self.sig.inputs.len();
        let arg1 = (0..).map(|i| format_ident!("arg{i}"));

        let ty = inputs.iter().flat_map(|x| match x {
            FnArg::Receiver(_) => None,
            FnArg::Typed(t) => Some(&t.ty)
        });
        let recv = self.sig.receiver();

        // Partials here contain filtered variants
        let mut partials = match &self.details.variant_marker {
            Some(marker) => {
                let mut partials = Vec::new();

                for v in &data.variants {
                    if verify_marker(&v.attrs, marker)? {
                        partials.push(v);
                    }
                }

                partials
            },
            None => data.variants.iter().collect()
        }.into_iter();

        let code = if recv.is_some() {
            if self.details.variant_aggregate.is_some() {
                return Err(Error::new(self.details.span, "in non-associated functions, variant aggregate is invalid"));
            }

            if self.details.variant_marker.is_some() {
                return Err(Error::new(self.details.span, "in non-associated functions, variant marker filter is invalid"));
            }

            if self.details.variant_init.is_some() {
                return Err(Error::new(self.details.span, "in non-associated functions, variant init expr is invalid"));
            }

            let v_id = partials.clone().map(|x| &x.ident);
            let destructured = partials.clone().map(|variant| {
                let field_var = (0..variant.fields.len()).map(|i| format_ident!("f{i}"));

                match &variant.fields {
                    Fields::Named(named) => {
                        let field_name = named.named.iter().map(|f| &f.ident);

                        quote! {
                            {
                                #(#field_name: #field_var),*
                            }
                        }
                    }
                    Fields::Unnamed(_) => {
                        quote! {
                            (#(#field_var)*)
                        }
                    }
                    Fields::Unit => quote!{}
                }
            });
            let mut variant_code = Vec::new();

            for variant in partials {
                let over = self.details.override_marker
                    .as_ref()
                    .map(|marker| verify_override(&variant.attrs, marker))
                    .transpose()?
                    .flatten()
                    .map(|func| {
                        let field_var = (0..variant.fields.len()).map(|i| format_ident!("f{i}"));
                        let arg2 = (0..).take(arg_count-1).map(|x| format_ident!("arg{x}"));
                        Ok::<_, Error>(quote! {(#func)(#(#field_var,)* #(#arg2,)* #variadic)})
                    })
                    .unwrap_or_else(
                        || {
                            let code = self.derive_fields(&variant.fields, trait_path, &question)?;
                            let v = &variant.ident;
                            if self.details.aggregate == Some(Aggregate::Construct) {
                                Ok(quote! {
                                    Self::#v #code
                                })
                            } else {
                                Ok(code)
                            }
                        }
                    )?;

                variant_code.push(over);
            }

            quote! {
                match self {
                    #(Self::#v_id #destructured => #variant_code,)*
                }
            }
        } else if self.details.aggregate == Some(Aggregate::Construct) {
            // associated constructive (no override allowed)
            if let Some(variant) = partials.next() {
                let v_id = &variant.ident;
                let construct = self.derive_fields(&variant.fields, trait_path, &question)?;
                quote! {
                    Self::#v_id #construct
                }
            } else {
                return Err(Error::new(data.variants.span(), "one variant must be marked for construction"))
            }
        } else {
            // associated non-constructive
            let mut variant_code = self.details.variant_init.as_ref()
                .map_or_else(Vec::new, |init| vec![quote! { #init }]);

            for variant in partials {
                let over = self.details.override_marker
                    .as_ref()
                    .map(|marker| verify_override(&variant.attrs, marker))
                    .transpose()?
                    .flatten()
                    .map(|func| {
                        let arg2 = (0..).take(arg_count).map(|x| format_ident!("arg{x}"));
                        Ok(quote! {(#func)(#(#arg2,)* #variadic)})
                    })
                    .unwrap_or_else(
                        || self.derive_fields(&variant.fields, trait_path, &question)
                    )?;

                variant_code.push(over);
            }

            if let Some(aggregate) = self.details.variant_aggregate {
                variant_code
                    .into_iter()
                    .reduce(|x, y| aggregate.aggregate(x, y))
                    .expect("expected a variant")
            } else {
                variant_code
                    .into_iter()
                    .next()
                    .expect("expected a variant")
            }
        };

        let code = wrap(&self.details.wrap, code);

        let recv = recv.map(|x| quote! {#x,});

        Ok(quote! {
            #constness #asyncness #unsafety #abi fn #ident #generics(#recv #(#arg1: #ty,)* #variadic) #output #where_clause {
                #code
            }
        })
    }
}

struct TraitImpl {
    generics: Generics,
    trait_: Path,
    self_generics: Option<AngleBracketedGenericArguments>,
    functions: Vec<FuncImpl>,
}

impl Parse for TraitImpl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        input.parse::<Token![impl]>()?;
        let mut generics: Generics = input.parse()?;
        let trait_ = input.parse()?;
        input.parse::<Token![for]>()?;
        input.parse::<Token![Self]>()?;
        let self_generics = if input.peek(Token![<]) {
            Some(input.parse()?)
        } else {
            None
        };
        generics.where_clause = input.parse()?;
        let content;
        braced!(content in input);

        let mut functions = Vec::new();

        while !content.is_empty() {
            functions.push(content.parse()?);
        }

        Ok(Self {
            generics,
            trait_,
            self_generics,
            functions
        })
    }
}

impl TraitImpl {
    fn derive<T, F: Fn(FuncImpl, &Path, &T) -> syn::Result<TokenStream2>>(self, ident: &Ident, data: &T, derive_fn: F) -> syn::Result<TokenStream2> {
        let Self {
            mut generics,
            trait_,
            self_generics,
            functions
        } = self;
        let where_clause = generics.where_clause.take();

        let mut impls = Vec::new();

        for f in functions {
            let imp = derive_fn(f, &trait_, data)?;
            // panic!("{imp}");
            impls.push(imp);
        }

        Ok(quote! {
            impl #generics #trait_ for #ident #self_generics #where_clause {
                #(#impls)*
            }
        })
    }

    fn derive_struct(self, ident: &Ident, data: &DataStruct) -> syn::Result<TokenStream2> {
        self.derive(ident, data, |f, tr, data| f.derive_struct(tr, data))
    }

    fn derive_enum(self, ident: &Ident, data: &DataEnum) -> syn::Result<TokenStream2> {
        self.derive(ident, data, |f, tr, data| f.derive_enum(tr, data))
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Aggregate {
    Construct,
    NoConstruct(NoConstructAggregate)
}

#[derive(Debug, Eq, PartialEq)]
enum NoConstructAggregate {
    Func(Path),
    Op(AggrOp)
}

impl NoConstructAggregate {
    fn aggregate(&self, x: TokenStream2, y: TokenStream2) -> TokenStream2 {
        match self {
            Self::Func(path) => quote! {
                #path(#x, #y)
            },
            Self::Op(op) => match op {
                AggrOp::BitOr => quote! { ({#x | #y}) },
                AggrOp::BitAnd => quote! { ({#x & #y}) },
                AggrOp::LogicOr => quote! { ({#x || #y}) },
                AggrOp::LogicAnd => quote! { ({#x && #y}) },
                AggrOp::Add => quote! { ({#x + #y}) },
                AggrOp::Mul => quote! { ({#x * #y}) },
                AggrOp::Unit => quote! { ({#x; #y}) }
            }
        }
    }
}

impl Parse for Aggregate {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(token::Brace) {
            let content;
            let span = braced!(content in input).span.span();
            if content.is_empty() {
                Ok(Self::Construct)
            } else {
                Err(Error::new(span, "expected empty brace"))
            }
        } else {
            Ok(Self::NoConstruct(input.parse()?))
        }
    }
}

impl Parse for NoConstructAggregate {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(Token!(||)) {
            input.parse::<Token!(||)>()?;
            Ok(Self::Op(AggrOp::LogicOr))
        } else if input.peek(Token!(&&)) {
            input.parse::<Token!(&&)>()?;
            Ok(Self::Op(AggrOp::LogicAnd))
        } else if input.peek(Token!(|)) {
            input.parse::<Token!(|)>()?;
            Ok(Self::Op(AggrOp::BitOr))
        } else if input.peek(Token!(&)) {
            input.parse::<Token!(&)>()?;
            Ok(Self::Op(AggrOp::BitAnd))
        } else if input.peek(Token![+]) {
            input.parse::<Token![+]>()?;
            Ok(Self::Op(AggrOp::Add))
        } else if input.peek(Token![*]) {
            input.parse::<Token![*]>()?;
            Ok(Self::Op(AggrOp::Mul))
        } else if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            Ok(Self::Op(AggrOp::Unit))
        }  else {
            return Ok(Self::Func(input.parse().map_err(|err| Error::new(err.span(), "valid operator or path expected"))?));
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum AggrOp {
    BitOr,
    BitAnd,
    LogicOr,
    LogicAnd,
    Add,
    Mul,
    Unit
}

enum Wrap {
    Result,
    Option
}

fn wrap(wrap: &Option<Wrap>, code: TokenStream2) -> TokenStream2 {
    match wrap {
        Some(Wrap::Result) => quote! { std::result::Result::Ok({#code}) },
        Some(Wrap::Option) => quote! { std::option::Option::Some({#code}) },
        None => code
    }
}

impl Parse for Wrap {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident: Ident = input.parse()?;

        match ident.to_string().as_str() {
            "Option" => Ok(Self::Option),
            "Result" => Ok(Self::Result),
            _ => Err(Error::new(ident.span(), "invalid wrap type, expected 'Option' or 'Result'"))
        }
    }
}

struct Details {
    marker: Option<Ident>,
    aggregate: Option<Aggregate>,
    init: Option<Expr>,
    variant_marker: Option<Ident>,
    variant_aggregate: Option<NoConstructAggregate>,
    variant_init: Option<Expr>,
    wrap: Option<Wrap>,
    span: Span,
    override_marker: Option<Ident>
}

impl Parse for Details {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        let span = braced!(content in input).span.span();

        let mut marker = None;
        let mut aggregate = None;
        let mut variant_marker = None;
        let mut variant_aggregate = None;
        let mut wrap = None;
        let mut init = None;
        let mut variant_init = None;
        let mut override_marker = None;

        while !content.is_empty() {
            let key: Ident = content.parse()?;
            content.parse::<Token![=]>()?;

            match key.to_string().as_str() {
                "marker" => if marker.is_none() {
                    marker = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                "aggregate" => if aggregate.is_none() {
                    aggregate = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                "variant_marker" => if variant_marker.is_none() {
                    variant_marker = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                "variant_aggregate" => if variant_aggregate.is_none() {
                    variant_aggregate = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                "wrap" => if wrap.is_none() {
                    wrap = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                "init" => if init.is_none() {
                    init = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                "variant_init" => if variant_init.is_none() {
                    variant_init = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                "override_marker" => if override_marker.is_none() {
                    override_marker = Some(content.parse()?);
                } else {
                    return Err(Error::new(key.span(), "key defined twice"))
                },
                _ => return Err(Error::new(key.span(), "invalid key"))
            }

            if content.is_empty() {
                break
            } else {
                content.parse::<Token![,]>()?;
            }
        }

        if aggregate == Some(Aggregate::Construct) {
            if marker.is_some() {
                return Err(Error::new(span, "marker cannot be given when aggregate is '{}'"));
            }

            if variant_aggregate.is_some() {
                return Err(Error::new(span, "variant aggregate cannot be given when aggregate is '{}'"));
            }

            if init.is_some() {
                return Err(Error::new(span, "init expr cannot be given when aggregate is '{}'"));
            }

            if variant_init.is_some() {
                return Err(Error::new(span, "init expr cannot be given when aggregate is '{}'"));
            }
        }

        Ok(Details {
            span,
            marker,
            aggregate,
            variant_marker,
            variant_aggregate,
            wrap,
            init,
            variant_init,
            override_marker
        })
    }
}

enum Marker {
    Ident(Ident),
    Override(Override)
}

struct Override {
    ident: Ident,
    _eq: Token![=],
    func: Expr
}

impl Parse for Marker {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident = input.parse()?;

        Ok(if input.is_empty() {
            Self::Ident(ident)
        } else {
            Self::Override(Override {
                ident,
                _eq: input.parse()?,
                func: input.parse()?
            })
        })
    }
}

fn verify_marker(attrs: &[Attribute], marker: &Ident) -> syn::Result<bool> {
    let mut found = false;

    for attr in attrs {
        if attr.meta.path().is_ident("recursive") {
            if let Meta::List(MetaList { tokens, .. }) = &attr.meta {
                if let Marker::Ident(id) = syn::parse2(tokens.clone())? {
                    found = id == *marker
                }
            } else {
                return Err(Error::new(attr.span(), "invalid macro usage"));
            }
        }
    }

    Ok(found)
}

fn verify_override(attrs: &[Attribute], marker: &Ident) -> syn::Result<Option<Expr>> {
    let mut found = None;

    for attr in attrs {
        if attr.meta.path().is_ident("recursive") {
            if let Meta::List(MetaList { tokens, .. }) = &attr.meta {
                if let Marker::Override(over) = syn::parse2(tokens.clone())? {
                    if over.ident == *marker {
                        if found.is_some() {
                            return Err(Error::new(attr.span(), "override defined twice"));
                        }

                        found = Some(over.func);
                    }
                }
            } else {
                return Err(Error::new(attr.span(), "invalid macro usage"));
            }
        }
    }

    Ok(found)
}

fn recursive_impl(input: DeriveInput) -> syn::Result<TokenStream2> {
    let ident = input.ident;

    let traits = input.attrs
        .into_iter()
        .filter(|attr| attr.meta.path().is_ident("recursive"))
        .map(|attr| {
            if let Meta::List(MetaList { tokens, .. }) = attr.meta {
                syn::parse2::<TraitImpl>(tokens)
            } else {
                panic!("invalid macro use")
            }
        });

    Ok(match input.data {
        Data::Struct(data) => {
            let mut impls = Vec::new();

            for tr in traits {
                impls.push(tr?.derive_struct(&ident, &data)?)
            }

            quote! {
                #(#impls)*
            }
        }
        Data::Enum(data) => {
            let mut impls = Vec::new();

            for tr in traits {
                impls.push(tr?.derive_enum(&ident, &data)?);
            }

            quote! {
                #(#impls)*
            }
        },
        Data::Union(u) => return Err(Error::new(u.fields.span(), "recursive does not work with unions"))
    })
}

#[proc_macro_derive(Recursive, attributes(recursive))]
pub fn recursive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let res = recursive_impl(input).unwrap_or_else(|err| err.into_compile_error());

    // panic!("{res}");
   res.into()
}
