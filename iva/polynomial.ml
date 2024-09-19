open Base

let flip_compare c x y = -c x y

let compare_pair compare_fst compare_snd (x1, y1) (x2, y2) =
  match compare_fst x1 x2 with 0 -> compare_snd y1 y2 | c -> c

let compare_list = List.compare

module type VAR = sig
  type t

  include Base.Comparable.S with type t := t

  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
  val pp : t Fmt.t
end

module Make (Var : VAR) (F : Fld.S) = struct
  (** Monomial *)
  module Mono = struct
    module T = struct
      type t = int Map.M(Var).t [@@deriving equal, sexp]
      (** A monomial is a map from variables to positive exponents. *)

      let pp_exponent : int Fmt.t =
        Fmt.using
          (fun n ->
            n
            |> Int.to_string
            |> String.to_list
            |> List.map ~f:(fun c ->
                   let i = Char.to_string c |> Int.of_string in
                   match i with
                   | 0 -> "⁰"
                   | 1 -> "¹"
                   | 2 -> "²"
                   | 3 -> "³"
                   | 4 -> "⁴"
                   | 5 -> "⁵"
                   | 6 -> "⁶"
                   | 7 -> "⁷"
                   | 8 -> "⁸"
                   | 9 -> "⁹"
                   | _ -> assert false)
            |> String.concat)
          Fmt.string

      let pp_var_exp ppf (var, exp) =
        let open Fmt in
        if exp = 1 then pf ppf "%a" Var.pp var
        else pf ppf "%a%a" Var.pp var pp_exponent exp

      let pp : t Fmt.t =
        let open Fmt in
        using (Map.to_alist ~key_order:`Decreasing) (hbox @@ list pp_var_exp)

      let invariant (m : t) = Map.for_all m ~f:(fun e -> e > 0)
      let normalize (m : t) : t = Map.filter m ~f:(fun e -> e > 0)

      let of_list : (Var.t * int) list -> t =
        Fn.compose normalize (Map.of_alist_exn (module Var))

      let to_list (m : t) = Map.to_alist m ~key_order:`Decreasing
      let one = Map.empty (module Var)

      let mul (m1 : t) (m2 : t) : t =
        Map.merge m1 m2 ~f:(fun ~key:_ -> function
          | `Left x | `Right x -> Some x
          | `Both (x, y) ->
              (* x, y > 0, so x+y > 0 *)
              Some (x + y))

      let deg (m : t) ~(of_ : Var.t) = Map.find m of_ |> Option.value ~default:0
      let total_deg (m : t) = Map.data m |> List.sum (module Int) ~f:Fn.id

      module IntRev = struct
        include Int

        let compare = flip_compare compare
      end

      let eval (v : Var.t -> F.t) (m : t) : F.t =
        Map.fold m ~init:F.one ~f:(fun ~key:var ~data:exp acc ->
            F.(acc * (v var ** Z.of_int exp)))

      let div (m1 : t) (m2 : t) : t option =
        let exception Indivisible in
        try
          let m =
            Map.merge m1 m2 ~f:(fun ~key:_ -> function
              | `Left x -> Some x
              | `Right _ -> raise Indivisible
              | `Both (x, y) ->
                  let e = x - y in
                  if e < 0 then raise Indivisible
                  else if e = 0 then None
                  else Some e)
          in
          Some m
        with Indivisible -> None

      let vars = Map.keys

      let compare_lex : t -> t -> int =
       fun m1 m2 ->
        let p1 = Map.to_alist m1 ~key_order:`Decreasing in
        let p2 = Map.to_alist m2 ~key_order:`Decreasing in
        [%compare: (Var.t * int) list] p1 p2

      let compare_grlex : t -> t -> int =
       fun m1 m2 ->
        let p1 = Map.to_alist m1 ~key_order:`Decreasing in
        let p2 = Map.to_alist m2 ~key_order:`Decreasing in
        let d1 = total_deg m1 in
        let d2 = total_deg m2 in
        [%compare: int * (Var.t * int) list] (d1, p1) (d2, p2)

      let compare_grrevlex : t -> t -> int =
       fun m1 m2 ->
        let p1 = Map.to_alist m1 ~key_order:`Increasing in
        let p2 = Map.to_alist m2 ~key_order:`Increasing in
        let d1 = total_deg m1 in
        let d2 = total_deg m2 in
        [%compare: int * (Var.t * IntRev.t) list] (d1, p1) (d2, p2)

      let compare = compare_lex
    end

    include T
    include Comparator.Make (T)

    module Lex = struct
      include T

      let compare = compare_lex

      include Comparable.Make (T)
    end

    module GrLex = struct
      include T

      let compare = compare_grlex

      include Comparable.Make (T)
    end

    module GrRevLex = struct
      include T

      let compare = compare_grrevlex

      include T
      include Comparable.Make (T)
    end

    let lex : (t, Lex.comparator_witness) Comparator.Module.t = (module Lex)

    let grlex : (t, GrLex.comparator_witness) Comparator.Module.t =
      (module GrLex)

    let grrevlex : (t, GrRevLex.comparator_witness) Comparator.Module.t =
      (module GrRevLex)
  end

  module Normal = struct
    type 'ord t = (Mono.t, F.t, 'ord) Map.t
    (** A polynomial is a map from monomials to non-zero field coefficients *)

    module Term = struct
      type t = Mono.t * F.t
      (** A term is a monomial and a coefficient *)

      let pp : t Fmt.t =
        let open Fmt in
        fun ppf (m, c) -> pf ppf "%a %a" F.pp c Mono.pp m

      let div (t1 : t) (t2 : t) : t option =
        let m1, c1 = t1 in
        let m2, c2 = t2 in
        match Mono.div m1 m2 with
        | None -> None
        | Some m -> Some (m, F.(c1 / c2))

      let deg (t : t) ~(of_ : Var.t) = Mono.deg (fst t) ~of_
      let total_deg (t : t) = Mono.total_deg (fst t)
      let invariant (t : t) = not F.(snd t = zero)
    end

    let terms (p : 'ord t) = Map.to_alist p ~key_order:`Decreasing

    let pp : type ord. ord t Fmt.t =
     fun (type ord) ppf (t : ord t) ->
      let open Fmt in
      using terms (list ~sep:(any " + ") Term.pp) ppf t

    let lift_term_fn f ~key ~data = f (key, data)
    let invariant (p : 'ord t) = Map.for_alli p ~f:(lift_term_fn Term.invariant)

    let normalize (p : 'ord t) : 'ord t =
      Map.filteri p ~f:(lift_term_fn Term.invariant)

    let of_terms comparator : Term.t list -> 'ord t =
      Fn.compose normalize (Map.of_alist_exn comparator)

    let reorder ordering : _ t -> 'ord t = Map.map_keys_exn ordering ~f:Fn.id
    let zero = Map.empty

    let total_deg (p : 'ord t) : int option =
      Map.keys p
      |> List.map ~f:Mono.total_deg
      |> List.max_elt ~compare:Int.compare

    let coeff (p : 'ord t) ~(of_ : Mono.t) : F.t =
      Map.find p of_ |> Option.value ~default:F.zero

    let vars (p : 'ord t) =
      p
      |> Map.keys
      |> List.concat_map ~f:Mono.vars
      |> List.dedup_and_sort ~compare:Var.compare

    let add (p1 : 'ord t) (p2 : 'ord t) : 'ord t =
      Map.merge p1 p2 ~f:(fun ~key:_ -> function
        | `Left x | `Right x -> Some x
        | `Both (x, y) -> if F.(x + y = zero) then None else Some F.(x + y))

    let comparator_of (p : 'ord t) = Map.comparator p |> Comparator.to_module
    let add_term (p : 'ord t) t = add p (of_terms (comparator_of p) [ t ])

    let mul : type ord. ord t -> ord t -> ord t =
     fun (type ord) (p1 : ord t) (p2 : ord t) : ord t ->
      Map.fold p1
        ~init:(zero (comparator_of p1))
        ~f:(fun ~key:m1 ~data:c1 acc ->
          Map.fold p2 ~init:acc ~f:(fun ~key:m2 ~data:c2 acc ->
              let m = Mono.mul m1 m2 in
              (* c ≠ 0 since c1, c2 ≠ 0 *)
              let c = F.(c1 * c2) in
              Map.change acc m ~f:(function
                | None -> Some c
                | Some c' ->
                    let c'' = F.(c + c') in
                    if F.(c'' = zero) then None else Some c'')))

    let mul_term (p : 'ord t) (t : Term.t) : 'ord t =
      mul p (of_terms (comparator_of p) [ t ])

    let neg p = Map.map p ~f:F.neg
    let sub p1 p2 = add p1 (neg p2)
    let ( + ) = add
    let ( +. ) = add_term
    let ( ~- ) = neg
    let ( - ) = sub
    let ( * ) = mul
    let ( *. ) = mul_term

    let eval (v : Var.t -> F.t) (p : 'ord t) : F.t =
      Map.fold p ~init:F.zero ~f:(fun ~key:m ~data:c acc ->
          F.(acc + (c * Mono.eval v m)))

    let leading_term (p : 'ord t) : (Mono.t * F.t) option = Map.max_elt p
    let leading_monomial p : Mono.t option = leading_term p |> Option.map ~f:fst
    let multideg p = leading_monomial p |> Option.map ~f:Mono.to_list
    let leading_coeff p : F.t option = leading_term p |> Option.map ~f:snd

    let div (p : 'ord t) (fs : 'ord t list) : 'ord t list * 'ord t =
      let fs = Array.of_list fs in
      let lt_fs = Array.map fs ~f:leading_term in
      let z = zero (comparator_of p) in
      let of_terms = of_terms (comparator_of p) in
      let rec aux p : 'ord t array * 'ord t =
        Logs.debug (fun m -> m "aux %a" pp p);
        match terms p with
        | [] -> (Array.init (Array.length fs) ~f:(Fn.const z), z)
        | lt_p :: ps -> (
            let p' = of_terms ps in
            match
              (* find the first f whose LT divides lt_p,
                 returning the index i the quotient lt_p / lt_f *)
              Array.find_mapi lt_fs
                ~f:
                  Option.Let_syntax.(
                    fun i lt_f_opt ->
                      lt_f_opt >>= fun lt_f ->
                      Term.div lt_p lt_f >>= fun q -> Some (i, q))
            with
            | None ->
                Logs.debug (fun m ->
                    m "no f divides %a, move to tail %a" Term.pp lt_p pp p');
                let qs, r = aux p' in
                (qs, r +. lt_p)
            | Some (i, q) ->
                let f = fs.(i) in
                Logs.debug (fun m ->
                    m "f_%d = %a divides %a, q = %a" i pp f Term.pp lt_p Term.pp
                      q);
                Logs.debug (fun m -> m "f * q = %a" pp (f *. q));
                Logs.debug (fun m -> m "p - f * q = %a" pp (p - (f *. q)));
                let qs, r = aux (p - (f *. q)) in
                qs.(i) <- qs.(i) +. q;
                (qs, r))
      in
      let qs, r = aux p in
      (Array.to_list qs, r)

    let ( / ) = div
    let ( // ) p t = div p t |> fst
    let ( mod ) p t = div p t |> snd
  end

  (** Polynomial in expression form *)
  module Expr = struct
    type t = Const of F.t | Var of Var.t | Add of t * t | Mul of t * t

    let ( + ) e1 e2 = Add (e1, e2)
    let ( * ) e1 e2 = Mul (e1, e2)
    let zero = Const F.zero
    let one = Const F.one

    let rec pp ppf = function
      | Const c -> F.pp ppf c
      | Var v -> Var.pp ppf v
      | Add (e1, e2) -> Fmt.pf ppf "(%a + %a)" pp e1 pp e2
      | Mul (e1, e2) -> Fmt.pf ppf "(%a * %a)" pp e1 pp e2

    let to_nf comparator =
      let rec go = function
        | Const c -> Normal.of_terms comparator [ (Mono.one, c) ]
        | Var v ->
            Normal.of_terms comparator [ (Mono.of_list [ (v, 1) ], F.one) ]
        | Add (e1, e2) -> Normal.add (go e1) (go e2)
        | Mul (e1, e2) -> Normal.mul (go e1) (go e2)
      in
      go

    let rec pow e n =
      if n = 0 then one else if n = 1 then e else e * pow e (n - 1)

    let of_mono (m : Mono.t) : t =
      let of_var_exp (var, exp) =
        List.init exp ~f:(Fn.const (Var var)) |> List.reduce_exn ~f:( * )
      in
      m
      |> Map.to_alist
      |> List.map ~f:of_var_exp
      |> List.reduce ~f:( * )
      |> Option.value ~default:zero

    let of_term (m, c) : t = Mul (Const c, of_mono m)

    let rec simplify = function
      | Const c -> Const c
      | Var v -> Var v
      | Add (e1, e2) -> (
          match (simplify e1, simplify e2) with
          | Const c1, Const c2 -> Const F.(c1 + c2)
          | (Const c, e | e, Const c) when F.(c = zero) -> e
          | e1', e2' -> Add (e1', e2'))
      | Mul (e1, e2) -> (
          match (simplify e1, simplify e2) with
          | Const c1, Const c2 -> Const F.(c1 * c2)
          | (Const c, e | e, Const c) when F.(c = one) -> e
          | (Const c, _ | _, Const c) when F.(c = zero) -> Const F.zero
          | e1', e2' -> Mul (e1', e2'))

    let of_nf (p : 'ord Normal.t) : t =
      p
      |> Normal.terms
      |> List.map ~f:(fun (m, c) -> Mul (Const c, of_mono m))
      |> List.reduce ~f:(fun acc e -> Add (acc, e))
      |> Option.value ~default:(Const F.zero)
      |> simplify

    let extreme_data dir ~measure =
      Map.fold ~init:None ~f:(fun ~key ~data -> function
        | None -> Some (key, data)
        | Some (key', data') ->
            if dir (measure data) (measure data') then Some (key, data)
            else Some (key', data'))

    let best_var _ (p : 'ord Normal.t) : Var.t option =
      let max_data = extreme_data ( > ) in
      let min_data = extreme_data ( < ) in
      let vars = Normal.vars p in
      (* mapping x -> mono -> deg of x in mono * coeff *)
      let degs =
        List.fold vars
          ~init:(Map.empty (module Var))
          ~f:(fun m x ->
            Map.add_exn m ~key:x
              ~data:
                (Map.mapi p ~f:(fun ~key:m ~data:c -> (Mono.deg m ~of_:x, c))))
      in
      max_data degs ~measure:(fun m ->
          let m = Map.filter m ~f:(fun (d, _) -> d > 0) in
          let _, (d, _) =
            min_data m ~measure:(fun (d, _) -> d) |> Option.value_exn
          in
          Int.(d * Map.length m))
      |> Option.map ~f:(fun (x, _) -> x)

    let next_var (vars : Var.t list) (p : 'ord Normal.t) : Var.t option =
      List.find vars ~f:(fun x ->
          (* x divides some monomial *)
          Map.existsi p ~f:(fun ~key:m ~data:_ -> Mono.deg m ~of_:x > 0))

    let horner (type ord) ?(heuristics = best_var) (p : ord Normal.t) : t =
      let comparator = Comparator.to_module (Map.comparator p) in
      let vars = Normal.vars p in
      let rec aux (p : ord Normal.t) : t =
        match heuristics vars p with
        | None -> Const (Normal.coeff p ~of_:Mono.one)
        | Some x ->
            let d =
              p
              |> Map.keys
              |> List.filter_map ~f:(fun m ->
                     let d = Mono.deg m ~of_:x in
                     Option.some_if (d > 0) d)
              |> List.min_elt ~compare:Int.compare
              |> Option.value_exn
            in
            Logs.debug (fun m -> m "heuristic: %a" Mono.pp_var_exp (x, d));

            (* partition terms according to whether they are divisible by x *)
            let divs, ndivs =
              List.partition_map (Normal.terms p) ~f:(fun (m, c) ->
                  match Mono.div m (Mono.of_list [ (x, d) ]) with
                  | Some m' -> Either.First (m', c)
                  | None -> Second (m, c))
            in
            let p = pow (Var x) d in
            Logs.debug (fun m -> m "pow %a %d = %a" Var.pp x d pp p);
            Add
              ( Mul (p, aux (Normal.of_terms comparator divs)),
                aux (Normal.of_terms comparator ndivs) )
            |> simplify
      in
      aux p

    let normalize comparator (e : t) : t = e |> to_nf comparator |> horner
  end
end

module Var = struct
  module T = struct
    include String

    let pp = Fmt.string
    let compare = flip_compare String.compare
  end

  include T
  include Comparable.Make (T)
end

module P = Make (Var) (Fld.Q)

let () = Logs.set_level (Some Logs.Debug)
let () = Logs.set_reporter (Logs_fmt.reporter ())

open Logs
open P
open Normal

let () =
  Logs.debug (fun m -> m "Test variable ordering");
  assert (Var.compare "x" "y" > 0);
  assert (Var.compare "y" "z" > 0);
  assert (Var.compare "x1" "x2" > 0)

let () =
  let open Mono in
  let m1 = of_list [ ("x", 3) ] in
  let m2 = of_list [ ("x", 2) ] in
  let m = div m1 m2 |> Option.value_exn in
  debug (fun mm -> mm "%a / %a = %a \n%!" P.Mono.pp m1 P.Mono.pp m2 P.Mono.pp m);
  assert (Mono.compare_lex m1 m2 > 0)

let () =
  (* x^3 y^2 z *)
  let m1 = Mono.of_list [ ("x", 3); ("y", 2); ("z", 1) ] in
  (* y^3 z^3 *)
  let m2 = Mono.of_list [ ("y", 3); ("z", 3) ] in
  assert (Mono.compare_lex m1 m2 > 0);
  (* x y z *)
  let m3 = Mono.of_list [ ("x", 1); ("y", 1); ("z", 1) ] in
  (* y^2 *)
  let m4 = Mono.of_list [ ("y", 2) ] in
  (* 2 m1 + 3/2 m2 - 3 m3 + 1 m4 *)
  let p =
    of_terms P.Mono.lex
      [
        (m1, Q.of_int 2);
        (m2, Q.(of_int 3 / of_int 2));
        (m3, Q.of_int (-3));
        (m4, Q.one);
      ]
  in

  debug (fun mm -> mm "p = %a\n%!" pp p);
  debug (fun mm -> mm "p * p = %a\n%!" pp (mul p p));
  debug (fun mm -> mm "horner (best) : %a\n%!" Expr.pp (Expr.horner p));
  debug (fun mm ->
      mm "horner (next) : %a\n%!" Expr.pp
        (Expr.horner ~heuristics:Expr.next_var p))

let () =
  (* x ^ 2 *)
  let p = P.Expr.(Var "x" * Var "x") in
  debug (fun mm -> mm "p = %a\n%!" P.Expr.pp p);
  debug (fun mm ->
      mm "normalize p = %a\n%!" P.Expr.pp (P.Expr.normalize P.Mono.lex p))

let () =
  Logs.debug (fun m -> m "Test lex");
  (* x y^2 *)
  let m1 = Mono.of_list [ ("x", 1); ("y", 2); ("z", 0) ] in
  (* y^3 z^4 *)
  let m2 = Mono.of_list [ ("y", 3); ("z", 4) ] in
  assert (Mono.compare_lex m1 m2 > 0);
  (* x^3 y^2 z^4 *)
  let m1 = Mono.of_list [ ("x", 3); ("y", 2); ("z", 4) ] in
  (* x^3 y^2 z^1 *)
  let m2 = Mono.of_list [ ("x", 3); ("y", 2); ("z", 1) ] in
  assert (Mono.compare_lex m1 m2 > 0);
  (* x2 z1 *)
  let m1 = Mono.of_list [ ("x", 2); ("z", 1) ] in
  (* x1 z2 *)
  let m2 = Mono.of_list [ ("x", 1); ("z", 2) ] in
  assert (Mono.compare_lex m1 m2 > 0)

let () =
  Logs.debug (fun m -> m "Test grlex");
  (* x y^2 z^3 *)
  let m1 = Mono.of_list [ ("x", 1); ("y", 2); ("z", 3) ] in
  (* x^3 t^2 z^0 *)
  let m2 = Mono.of_list [ ("x", 3); ("t", 2); ("z", 0) ] in
  assert (Mono.compare_grlex m1 m2 > 0);
  (* x y^2 z^4 *)
  let m1 = Mono.of_list [ ("x", 1); ("y", 2); ("z", 4) ] in
  (* x^3 y^2 z^1 *)
  (* x y z^5 *)
  let m2 = Mono.of_list [ ("x", 1); ("y", 2); ("z", 1) ] in
  assert (Mono.compare_grlex m1 m2 > 0);
  (* x5 y1 z1 *)
  let m1 = Mono.of_list [ ("x", 5); ("y", 1); ("z", 1) ] in
  (* x4 y1 z2 *)
  let m2 = Mono.of_list [ ("x", 4); ("y", 1); ("z", 2) ] in
  assert (Mono.compare_grlex m1 m2 > 0)

let () =
  Logs.debug (fun m -> m "Test grrevlex");
  (* x4 y7 z1 *)
  let m1 = Mono.of_list [ ("x", 4); ("y", 7); ("z", 1) ] in
  (* x4 y2 z3 *)
  let m2 = Mono.of_list [ ("x", 4); ("y", 2); ("z", 3) ] in
  assert (Mono.compare_grrevlex m1 m2 > 0);
  (* x1 y5 z2 *)
  let m1 = Mono.of_list [ ("x", 1); ("y", 5); ("z", 2) ] in
  (* x4 y1 z3 *)
  let m2 = Mono.of_list [ ("x", 4); ("y", 1); ("z", 3) ] in
  assert (Mono.compare_grrevlex m1 m2 > 0);
  (* x5 y1 z1 *)
  let m1 = Mono.of_list [ ("x", 5); ("y", 1); ("z", 1) ] in
  (* x4 y1 z2 *)
  let m2 = Mono.of_list [ ("x", 4); ("y", 1); ("z", 2) ] in
  assert (Mono.compare_grrevlex m1 m2 > 0)

let () =
  (* 4xy^2z + 4z^2 - 5x^3 + 7x^2z^2 *)
  let p =
    of_terms Mono.lex
      [
        (Mono.of_list [ ("x", 1); ("y", 2); ("z", 1) ], Q.of_int 4);
        (Mono.of_list [ ("z", 2) ], Q.of_int 4);
        (Mono.of_list [ ("x", 3) ], Q.of_int (-5));
        (Mono.of_list [ ("x", 2); ("z", 2) ], Q.of_int 7);
      ]
  in
  Logs.debug (fun m -> m "Test pp");
  Logs.debug (fun m -> m "Lex: %a" pp p);
  Logs.debug (fun m -> m "GrLex: %a" pp (reorder Mono.grlex p));
  Logs.debug (fun m -> m "GrRevLex: %a" pp (reorder Mono.grrevlex p))

let () =
  Logs.debug (fun m -> m "Test multideg");
  (* 4xy^2z + 4z^2 - 5x^3 + 7x^2z^2 *)
  let p =
    of_terms Mono.lex
      [
        (Mono.of_list [ ("x", 1); ("y", 2); ("z", 1) ], Q.of_int 4);
        (Mono.of_list [ ("z", 2) ], Q.of_int 4);
        (Mono.of_list [ ("x", 3) ], Q.of_int (-5));
        (Mono.of_list [ ("x", 2); ("z", 2) ], Q.of_int 7);
      ]
  in
  assert ([%equal: (Var.t * int) list option] (multideg p) (Some [ ("x", 3) ]));
  assert ([%equal: Q.t option] (leading_coeff p) (Some (Q.of_int (-5))));
  assert (
    [%equal: Mono.t option] (leading_monomial p)
      (Some (Mono.of_list [ ("x", 3) ])));
  (* leading term is -5x^3 *)
  assert (
    [%equal: (Mono.t * Q.t) option] (leading_term p)
      (Some (Mono.of_list [ ("x", 3) ], Q.of_int (-5))))

let () =
  Logs.debug (fun m -> m "Test div");
  (* p = xy^2 + 1
     f1 = xy + 1
     f2 = y + 1
  *)
  let p =
    Mono.(
      of_terms lex [ (of_list [ ("x", 1); ("y", 2) ], Q.one); (one, Q.one) ])
  in
  let f1 =
    Mono.(
      of_terms lex [ (of_list [ ("x", 1); ("y", 1) ], Q.one); (one, Q.one) ])
  in
  let f2 =
    Mono.(of_terms lex [ (of_list [ ("y", 1) ], Q.one); (one, Q.one) ])
  in
  let qs, r = p / [ f1; f2 ] in
  Logs.debug (fun m ->
      m "%a / %a = %a; %a" pp p pp f1 Fmt.(list ~sep:comma pp) qs pp r);
  (* p = x^2y + x y^2 + y^2
     f0 = xy - 1
     f1 = y^2 - 1
  *)
  let p =
    Mono.(
      of_terms lex
        [
          (of_list [ ("x", 2); ("y", 1) ], Q.one);
          (of_list [ ("x", 1); ("y", 2) ], Q.one);
          (of_list [ ("y", 2) ], Q.one);
        ])
  in
  let f0 =
    Mono.(
      of_terms lex
        [ (of_list [ ("x", 1); ("y", 1) ], Q.one); (one, Q.neg Q.one) ])
  in
  let f1 =
    Mono.(of_terms lex [ (of_list [ ("y", 2) ], Q.one); (one, Q.neg Q.one) ])
  in
  let qs, r = p / [ f0; f1 ] in
  Logs.debug (fun m ->
      m "%a / %a = %a; %a" pp p pp f0 Fmt.(list ~sep:comma pp) qs pp r)

(*
     let () =
       let open P in
       (* p1 = (2x-1) p2 = (5x - 6) *)
       let p1 =
         of_terms
           [ (Mono.of_list [ ("x", 1) ], F.of_int 2); (Mono.one, F.of_int (-1)) ]
       in
       let p2 =
         of_terms
           [ (Mono.of_list [ ("x", 1) ], F.of_int 5); (Mono.one, F.of_int (-6)) ]
       in
       debug (fun mm -> mm "%a * %a = %a\n%!" pp p1 pp p2 pp (mul p1 p2)

     let () =
       (* (2x^2-1)(-x^2-6) *)
       let open P in
       let p1 =
         P.of_terms
           [ (Mono.of_list [ ("x", 2) ], F.of_int 2); (Mono.one, F.of_int (-1)) ]
       in
       let p2 =
         P.of_terms
           [
             (Mono.of_list [ ("x", 2) ], F.of_int (-1)); (Mono.one, F.of_int (-6));
           ]
       in
       debug (fun mm -> mm "%a * %a = %a\n%!" P.pp p1 P.pp p2 P.pp (P.mul p1 p2) *)
