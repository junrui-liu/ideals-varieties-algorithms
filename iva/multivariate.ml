open Base
open Util

type index = int [@@deriving show, compare, equal, sexp]
type mindex = index list [@@deriving show, compare, equal, sexp]

module Order = struct
  let total = List.fold_left ~f:( + ) ~init:0
  let wf (alpha : mindex) : bool = List.for_all ~f:(fun i -> i >= 0) alpha

  let with_padding p q ~f =
    assert (wf p);
    assert (wf q);
    let pad xs l = xs @ List.init ~f:(Fn.const 0) (l - List.length xs) in
    let l = Int.max (List.length p) (List.length q) in
    f (pad p l) (pad q l)

  let add (alpha : mindex) (beta : mindex) =
    with_padding alpha beta ~f:(List.map2_exn ~f:( + ))

  let sub (alpha : mindex) (beta : mindex) =
    with_padding alpha beta ~f:(List.map2_exn ~f:( - ))

  module type S = sig
    type t = mindex [@@deriving ord, sexp]

    include Comparable.S with type t := t
  end

  module Lex : S with type t = mindex = struct
    module T = struct
      type t = mindex [@@deriving ord, sexp]

      let compare p q = with_padding p q ~f:compare
    end

    include T
    module C = Comparable.Make (T)
    include C
    module Infix : Comparable.Infix with type t := t = C
  end

  module GrLex : S with type t = mindex = struct
    module T = struct
      type t = mindex [@@deriving ord, sexp]

      let compare p q =
        let d = total p - total q in
        if d = 0 then Lex.compare p q else d
    end

    include T
    module C = Comparable.Make (T)
    include C
    module Infix : Comparable.Infix with type t := t = C
  end

  module GrevLex : S with type t = mindex = struct
    module T = struct
      type t = mindex [@@deriving ord, sexp]

      let compare p q =
        let d = total p - total q in
        if d = 0 then -Lex.compare (List.rev p) (List.rev q) else d
    end

    include T
    module C = Comparable.Make (T)
    include C
    module Infix : Comparable.Infix with type t := t = C
  end
end

open Core

module Simple (F : Algebra.FIELD) = struct
  type t = Const of F.t | Var of int | Mul of t * t | Add of t * t

  let rec eval (a : int -> F.t) : t -> F.t = function
    | Const c -> c
    | Var x -> a x
    | Mul (p, q) -> F.(eval a p * eval a q)
    | Add (p, q) -> F.(eval a p + eval a q)

  let const c = Const c
  let zero = const F.zero
  let v n = Var n
  let [ x; y; z ] = List.map ~f:v [ 0; 1; 2 ]

  let [ x0; x1; x2; x3; x4; x5; x6; x7; x8; x9 ] =
    List.map ~f:v (List.init ~f:Fn.id 10)

  let ( + ) p q = Add (p, q)
  let ( * ) p q = Mul (p, q)
  let ( #* ) c p = Mul (const c, p)
  let ( - ) p q = p + (F.(-one) #* q)

  let rec ( ^ ) p i =
    if i = 0 then const F.one else if i = 1 then p else p * (p ^ Int.(i - 1))

  let rec show = function
    | Const c -> F.show c
    | Var i -> Format.sprintf "x%d" i
    | Add (p, q) -> Format.sprintf "(%s + %s)" (show p) (show q)
    | Mul (p, q) -> Format.sprintf "(%s * %s)" (show p) (show q)
end

module M = Map.Make (Order.Lex)

module Coeff (F : Algebra.FIELD) = struct
  type t = F.t M.t

  exception ZeroPolynomial of t
  exception Abnormal of string

  type mdegree =
    (mindex
    [@printer
      fun ppf mdegree ->
        Fmt.(
          list ~sep:nop (fun fmt (i, n) ->
              if n > 0 then
                (pair ~sep:nop
                   (any " "
                   ++
                   match i with
                   | 0 -> const string "x"
                   | 1 -> const string "y"
                   | 2 -> const string "z"
                   | _ -> const string "x" ++ int)
                   (if n = 1 then nop else const string "^" ++ int))
                  fmt (i, n)
              else cut fmt ())
          ++ any " ")
          ppf (Util.number mdegree)])
  [@@deriving show, eq, ord, sexp]

  let equal_monomial = equal_mdegree

  let pp_debug : t Fmt.t =
    Util.pp_of_show @@ fun f ->
    M.to_alist ~key_order:`Decreasing f |> [%derive.show: (mdegree * F.t) list]

  type mono =
    (mdegree * F.t
    [@printer
      fun ppf (m, c) ->
        if F.(c = one) && (not @@ List.is_empty m) then
          Fmt.(parens pp_mdegree) ppf m
        else Fmt.(pf ppf "(%a%a)" F.pp c pp_mdegree m)])
  [@@deriving show, eq]

  let pp : t Fmt.t =
   fun ppf f ->
    if M.is_empty f then Fmt.string ppf "0"
    else
      Fmt.(list ~sep:(any " + ") pp_mono)
        ppf
        (M.to_alist ~key_order:`Decreasing f)

  let is_normal : t -> bool = M.for_all ~f:(Fn.compose not F.(equal zero))

  let assert_normal (f : t) =
    if not (is_normal f) then raise (Abnormal (Fmt.str "%a" pp_debug f))

  let with_normal (f : t) : t =
    assert_normal f;
    f

  let normalize : t -> t = M.filter ~f:(not <.> F.(equal zero))
  let const c : t = if F.(c = zero) then M.empty else M.singleton [] c
  let ( ^ ) = const
  let zero : t = M.empty

  let xi i =
    M.singleton (List.init (i + 1) ~f:(fun j -> if j = i then 1 else 0)) F.one

  let [ x; y; z ] = List.map ~f:xi [ 0; 1; 2 ]

  let equal (f : t) (g : t) : bool =
    assert_normal f;
    assert_normal g;
    M.equal F.equal f g

  let add (f : t) (g : t) : t =
    assert_normal f;
    assert_normal g;
    with_normal
    @@ M.merge f g
         ~f:
           F.(
             fun ~key:_ -> function
               | `Both (a, b) -> create_option_if (a + b) ~f:(not <.> equal zero)
               | `Left c | `Right c -> Some c)

  let ( + ) = add

  let neg (f : t) : t =
    assert_normal f;
    with_normal @@ M.map f ~f:F.neg

  let ( ~- ) = neg

  let sub (f : t) (g : t) : t =
    assert_normal f;
    assert_normal g;
    with_normal @@ (f + -g)

  let ( - ) = sub

  let mul (f : t) (g : t) : t =
    assert_normal f;
    assert_normal g;
    (* Fmt.pr "f=%a * g=%a\n%!" pp_debug f pp_debug g ; *)
    (* List.cartesian_product (M.to_alist f) (M.to_alist g) |> List.fold ~init:zero
       ~f:(fun p ((alpha, a), (beta, b)) ->
         let gamma = Order.add alpha beta in
         let ab = F.(a * b) in
         Fmt.pr "(a=%a, alpha=%a) * (b=%a, beta=%a) = (ab=%a, gamma=%a)\n%!" F.pp
           a pp_mdegree alpha F.pp b pp_mdegree beta F.pp ab pp_mdegree gamma ;
         M.change p gamma ~f:(function
           | Some c ->
               Fmt.pr "Previous c=%a\n%!" F.pp c ;
               Some F.(ab + c)
           | _ ->
               Some ab ) ) *)
    with_normal
    @@ M.fold f ~init:zero ~f:(fun ~key:alpha ~data:a p ->
           M.fold g ~init:p ~f:(fun ~key:beta ~data:b q ->
               let gamma = Order.add alpha beta in
               let ab = F.(a * b) in
               M.change q gamma ~f:(function
                 | Some c -> Some F.(ab + c)
                 | _ -> Some ab)))

  let ( * ) = mul

  let pow (f : t) (n : int) : t =
    assert_normal f;
    with_normal
    @@ List.fold (List.init n ~f:Fn.id) ~init:(const F.one) ~f:(fun p _ ->
           p * f)

  let ( ^ ) = pow
  let of_alist = M.of_alist_exn

  let lex (f : t) : (mdegree * F.t) list =
    M.to_alist f
    |> List.sort ~compare:(fun (a, _) (b, _) -> Int.neg (Order.Lex.compare a b))

  let grlex (f : t) : (mdegree * F.t) list =
    M.to_alist f
    |> List.sort ~compare:(fun (a, _) (b, _) ->
           Int.neg (Order.GrLex.compare a b))

  let grevlex (f : t) : (mdegree * F.t) list =
    M.to_alist f
    |> List.sort ~compare:(fun (a, _) (b, _) ->
           Int.neg (Order.GrevLex.compare a b))

  let equal = M.equal F.equal
  let ( = ) = equal
  let multidegree (f : t) = List.max_elt ~compare:Order.Lex.compare (M.keys f)
  let leading_term (f : t) : mono = M.max_elt_exn f
  let leading_monomial (f : t) = fst (leading_term f)
  let leading_coeff (f : t) = snd (leading_term f)

  let divide_mono (f : mono) (g : mono) : mono option =
    let m, c = f in
    let n, d = g in
    if Order.with_padding m n ~f:(List.for_all2_exn ~f:Int.( >= )) then
      let m' = Order.sub m n in
      Some (m', F.(c / d))
    else None

  let lift (f : mono) : t =
    let m, c = f in
    M.singleton m c

  let div (f : t) (fs : t list) : t list * t =
    let rec aux (p : t) : t list * t =
      if p = zero then (List.init (List.length fs) ~f:(Fn.const zero), zero)
      else
        (* Fmt.pr ">>> p=%a\n%!" pp p ; *)
        let p_lt = leading_term p in
        match
          List.find_mapi fs ~f:(fun i fi ->
              Option.map
                ~f:(fun gi ->
                  (* Fmt.pr "> i=%d, gi=%a, fi=%a, LT(fi)=%a\n%!" i pp_mono gi pp
                     fi pp_mono (leading_term fi) ; *)
                  (i, gi, fi))
                (divide_mono p_lt (leading_term fi)))
        with
        | Some (i, gi, fi) ->
            let qs, r = aux (p - (lift gi * fi)) in
            ( List.mapi ~f:(fun j q -> if Int.(i = j) then q + lift gi else q) qs,
              r )
        | None ->
            let qs, r = aux (p - lift p_lt) in
            (qs, r + lift p_lt)
    in
    aux f
end
