open Core
open Fmt

(* Example usage *)

module Simple (F : Algebra.FIELD) = struct
  type t = Const of F.t | Var | Mul of t * t | Add of t * t

  let rec eval (a : F.t) : t -> F.t = function
    | Const c -> c
    | Var -> a
    | Mul (p, q) -> F.(eval a p * eval a q)
    | Add (p, q) -> F.(eval a p + eval a q)

  let const c = Const c
  let zero = const F.zero
  let x = Var
  let ( + ) p q = Add (p, q)
  let ( * ) p q = Mul (p, q)
  let ( #* ) c p = Mul (const c, p)
  let ( - ) p q = p + (F.(-one) #* q)

  let rec ( ^ ) p i =
    if i = 0 then const F.one else if i = 1 then p else p * (p ^ Int.(i - 1))

  let rec pp : t Fmt.t =
   fun fmt -> function
    | Const c -> F.pp fmt c
    | Var -> Fmt.string fmt "x"
    | Add (p, q) ->
        Fmt.(parens (const pp p ++ sp ++ const string "+" ++ sp ++ const pp q))
          fmt ()
    | Mul (p, q) ->
        Fmt.(parens (const pp p ++ sp ++ const string "*" ++ sp ++ const pp q))
          fmt ()

  let show = Util.show_of_pp pp
end

module Coeff (F : Algebra.FIELD) = struct
  (* Invariant: most significant coefficients first, no leading zeros *)
  type t = F.t list

  exception ZeroPolynomial of t

  let const c = [ c ]
  let zero : t = []
  let x : t = [ F.one; F.zero ]

  let nz (f : t) (a : F.t -> t -> 'a) : 'a =
    match f with [] -> raise (ZeroPolynomial f) | c :: f' -> a c f'

  type degree = int

  let rec deg (f : t) : degree = nz f (fun _ -> List.length)
  let equal : t -> t -> bool = List.equal F.( = )
  let ( = ) = equal
  let to_lsb = List.rev
  let to_msb = List.rev

  let eval (a : F.t) (f : t) : F.t =
    let rec run = function [] -> F.zero | c :: f -> F.(c + (a * run f)) in
    run (List.rev f)

  let normalize : t -> t = List.drop_while ~f:F.(equal zero)
  let is_normal (f : t) : bool = Int.(List.length (normalize f) = List.length f)

  let show_debug f =
    Format.sprintf "[%s]" (String.concat ~sep:", " (List.map ~f:F.show f))

  let show (f : t) =
    let show_coeff c = F.(if c = one then "" else F.show c) in
    let show_mono c i =
      match i with
      | 0 -> F.show c
      | 1 -> Format.sprintf "%sx" (show_coeff c)
      | _ -> Format.sprintf "%sx^%d" (show_coeff c) i
    in
    let rec run f (i : int) =
      match f with
      | [] -> []
      | c :: f' ->
          if F.(c = zero) then run f' Int.(i - 1)
          else
            let rest = run f' Int.(i - 1) in
            show_mono c i
            ::
            (if List.is_empty rest then []
             else
               (if (Char.equal (String.get (List.hd_exn rest) 0)) '-' then " "
                else " + ")
               :: rest)
    in
    if f = zero then "0" else String.concat ~sep:"" (run f (deg f))

  let debug f r =
    f r;
    r

  let debug_with r f = f r

  let add_lsb (f : t) (g : t) : t =
    let rec run f g =
      match (f, g) with
      | [], _ -> g
      | _, [] -> f
      | c :: f', d :: g' -> F.(c + d) :: run f' g'
    in
    (* debug (fun r -> Printf.printf "%s +. %s = \t%s\n%!" (show_debug f) (show_debug g) (show_debug r))  *)
    run f g

  let add_msb (f : t) (g : t) : t =
    add_lsb (to_lsb f) (to_lsb g) |> to_msb |> normalize

  let ( + ) = add_msb
  let ( +. ) = add_lsb

  let scale_lsb (x : F.t) (f : t) : t =
    (* debug (fun r -> Printf.printf "%s #* %s = \t%s\n%!" (F.show x) (show_debug f) (show_debug r)) *)
    List.map ~f:(F.mul x) f

  let scale_msb x f = scale_lsb x f |> normalize
  let ( #* ) = scale_msb
  let ( #*. ) = scale_lsb
  let ( - ) f g = f + (F.(-one) #* g)
  let ( -. ) f g = f +. (F.(-one) #* g)

  let mul_lsb (f : t) (g : t) : t =
    let rec run f g =
      match (f, g) with
      | [], _ -> []
      | _, [] -> []
      | c :: f', d :: g' ->
          (* (c + xF)(d + xG) = cd + x(cG + dF + xFG)  *)
          let cg' = c#*.g' in
          let df' = d#*.f' in
          let rest = run f' g' in
          F.(c * d) :: (cg' +. df' +. (F.zero :: rest))
    in
    run f g

  let mul_msb f g = mul_lsb (to_lsb f) (to_lsb g) |> to_msb |> normalize
  let ( * ) = mul_msb
  let ( *. ) = mul_lsb

  let rec ( ^ ) p i =
    if Int.(i = 0) then const F.one
    else if Int.(i = 1) then p
    else p * (p ^ Int.(i - 1))

  let rec from_simple : Simple(F).t -> t = function
    | Const c -> [ c ]
    | Var -> [ F.one; F.zero ]
    | Add (p, q) -> from_simple p + from_simple q
    | Mul (p, q) -> from_simple p * from_simple q

  type monomial = F.t * int

  let from_mono (c, d) : t = c :: List.init d ~f:(fun _ -> F.zero)
  let leading_term (f : t) : monomial = nz f (fun c _ -> (c, deg f))

  let div_mono ((c, d) : monomial) ((c', d') : monomial) : monomial =
    (F.(c / c'), Int.(d - d'))

  let div (f : t) (g : t) : t * t =
    if g = zero then raise (ZeroPolynomial g);
    let lt_g = leading_term g in
    let rec run (f : t) =
      (* Printf.printf "div %s %s\n%!" (show f) (show g) ; *)
      if f = zero then (zero, zero)
      else if deg f < deg g then (zero, f)
      else
        let lt_f = leading_term f in
        let a = from_mono (div_mono lt_f lt_g) in
        (* Printf.printf "lt(%s)/lt(%s) = %s\n%!" (show f) (show g) *)
        (* (show a) ; *)
        (* Printf.printf "f - ag = %s\n%!" (show (f - (a * g))); *)
        let q, r = run (f - (a * g)) in
        (a + q, r)
    in
    (* debug (fun (q,r) ->  *)
    (* Printf.printf "div (%s, %s) =\t(%s, %s)\n%!" (show f) (show g) (show q) (show r)) *)
    run f

  let ( /% ) = div
  let ( / ) f g = f /% g |> fst
  let ( % ) f g = f /% g |> snd
  let rec gcd (f : t) (g : t) : t = if g = zero then f else gcd g (f % g)

  let rec ext_euclid (f : t) (g : t) : t * (t * t) =
    if g = zero then (f, (const F.one, zero))
    else
      let q, r = div f g in
      let gcd, (c, d) = ext_euclid g r in
      let a, b = (d, c - (d * q)) in
      assert ((a * f) + (b * g) = gcd);
      (gcd, (a, b))

  let gcds (fs : t list) : t =
    List.fold_left fs ~init:zero ~f:(fun f d -> gcd f d)

  let mem (f : t) (gs : t list) : bool =
    let d = gcds gs in
    f % d = zero

  let consistent (fs : t list) : bool =
    let d = gcds fs in
    d = zero || Int.(deg d = 0)

  let rec derivative_lsb (f : t) : t =
    match f with [] -> [] | _ :: r -> r + (F.zero :: derivative_lsb r)

  let derivative_msb (f : t) : t =
    f |> to_lsb |> derivative_lsb |> to_msb |> normalize

  let ( ~. ) = derivative_msb

  let reduce (f : t) : t =
    let f' = ~.f in
    let d = gcd f f' in
    let q, r = f /% d in
    assert (r = zero);
    q

  let nsatz (fs : t list) : t = reduce (gcds fs)
end

module SQ = struct
  module SimpleFQ = Simple (Algebra.FQ)
  include SimpleFQ

  let const n = SimpleFQ.const (Q.of_int n)
end

module CQ = struct
  module CoeffFQ = Coeff (Algebra.FQ)
  include CoeffFQ

  let const (n : int) = const (Q.of_int n)
end

(* let _ = CQ.((x^2) + const 1 |> show |> print_endline) *)

(* let _ = CQ.(const 1 * ((x^2)) |> show |> print_endline) *)

open CQ

let g = (x ^ 6) - const 1
let f = (x ^ 4) - const 1

(* let _ = gcd f g |> show |> print_endline
   let _ = gcds [f] |> show |> print_endline
   let _ = gcds [f; g] |> show |> print_endline *)

(* let _ =
     gcds
       [ (x ^ 4) + (x ^ 2) + const 1
       ; (x ^ 4) - (x ^ 2) - (const 2 * x) - const 1
       ; (x ^ 3) - const 1 ]
     |> show |> print_endline

   let _ =
     gcds
       [ (x ^ 3) + (const 2 * (x ^ 2)) - x - const 2
       ; (x ^ 3) - (const 2 * (x ^ 2)) - x + const 2
       ; (x ^ 3) - (x ^ 2) - (const 4 * x) + const 4 ]
     |> show |> print_endline *)

(* let _ = gcd ((x ^ 2) + const 1) ((x ^ 2) + const 2) |> show |> print_endline *)
(* let _ =
   mem ((x^2) - const 4)
     [
       (x ^ 3) + (x ^ 2) - (const 4 * x) - const 4
     ; (x ^ 3) - (x ^ 2) - (const 4 * x) + const 4
     ; (x ^ 3) - (const 2 * (x ^ 2)) - x + const 2
     ]
    |> Bool.to_string |> print_endline *)

(* let (h,(a,b)) = ext_euclid f g;; *)
(* Format.printf "(%s) %s + (%s) %s = %s = gcd\n%!" (show a) (show f) (show b) (show g) (show h                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ) *)

let f = List.init 5 ~f:(fun i -> Q.of_int Int.((5 - i) * 10))
let f' = ~.f
let _ = Printf.printf "d (%s) = %s\n%!" (show f) (show f')

let f =
  (x ^ 11)
  - (x ^ 10)
  + (const 2 * (x ^ 8))
  - (const 4 * (x ^ 7))
  + (const 3 * (x ^ 5))
  - (const 3 * (x ^ 4))
  + (x ^ 3)
  + (const 3 * (x ^ 2))
  - x
  - const 1
;;

print_endline (show f);;
print_endline (show (reduce f))

let f1 = (x ^ 5) - (const 2 * (x ^ 4)) + (const 2 * (x ^ 2)) - x

let f2 =
  (x ^ 5) - (x ^ 4) - (const 2 * (x ^ 3)) + (const 2 * (x ^ 2)) + x - const 1
;;

print_endline (show f1);;
print_endline (show f2);;
print_endline (show (nsatz [ f1; f2 ]));;
print_endline (show (gcd f1 f2));;

let r = (x ^ 2) - const 1 in
print_endline (show (gcd f1 f2 % r))

(* Bool.to_string (mem ((x ^ 2) - const 1) [f1; f2]) |> print_endline *)
