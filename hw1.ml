(* P1 *)

module Q = struct
  type t = int * int

  let abs m = if m >= 0 then m else -m
  let rec gcd m n = if n = 0 then abs m else gcd n (m mod n)

  (* Problem *)
  let is_q (m, n) = n > 0 && gcd m n = 1

  let normalize (m, n) : t =
    let r = gcd m n in
    (m / r, n / r)

  (* Problem *)
  let from_int (n : int) : t = (n, 1)
  let zero : t = from_int 0
  let one : t = from_int 1

  (* Problem *)
  let equal ((a, b) : t) ((c, d) : t) : bool = Int.equal a b && Int.equal c d

  (* Problem *)
  let add ((a, b) : t) ((c, d) : t) : t = normalize ((a * d) + (b * c), b * d)

  (* Problem *)
  let mul ((a, b) : t) ((c, d) : t) : t = normalize (a * c, b * d)
  let neg ((a, b) : t) : t = (-a, b)
  let sub r s : t = add r (mul (neg one) s)

  (* Problem *)
  let inv ((a, b) : t) : t option =
    if a = 0 then None else if a < 0 then Some (-b, -a) else Some (b, a)

  (* Problem *)
  let div r s : t option =
    match inv s with None -> None | Some s_inv -> Some (mul r s_inv)

  let ( + ) = add
  let ( * ) = mul
  let ( - ) = sub
  let ( ! ) = inv
  let ( / ) = div

  let show ((a, b) : t) : string =
    if b = 1 then Int.to_string a else Format.sprintf "%d/%d" a b

  let print (r : t) : unit = print_endline (show r)

  (* TODO digits (assuming termination), bounded digits *)
end

module Tree = struct
  type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree

  let to_list (t : 'a tree) : 'a list =
    let rec helper acc = function
      | Leaf -> acc
      | Node (x, l, r) -> helper (helper (x :: acc) r) l
    in
    helper [] t

  let to_tree (xs : 'a list) (n : int) : 'a tree =
    let rec helper xs n : 'a tree * 'a list =
      match xs with
      | [] -> (Leaf, [])
      | x :: xs' ->
          let l, ls = helper xs' (n - 1) in
          let r, rs = helper ls (n - 1) in
          (Node (x, l, r), rs)
    in
    fst (helper xs n)

  type direction = Left | Right

  let rec navigate_bst (t : int tree) (n : int) : direction list option =
    match t with
    | Leaf -> None
    | Node (m, l, r) ->
        if m = n then Some []
        else if m < n then Option.map (List.cons Left) (navigate_bst l n)
        else Option.map (List.cons Right) (navigate_bst r n)

  let rec navigate (t : int tree) (n : int) : direction list option =
    match t with
    | Leaf -> None
    | Node (m, l, r) -> (
        if m = n then Some []
        else
          match navigate l n with
          | None -> Option.map (List.cons Right) (navigate r n)
          | r -> Option.map (List.cons Left) r)
end

module Boolean = struct
  type exp =
    | Var : int -> exp
    | Neg : exp -> exp
    | And : exp * exp -> exp
    | Or : exp * exp -> exp
    | Imply : exp * exp -> exp

  type value = True | False

  let rec eval (e : exp) (a : int -> value) : value =
    match e with
    | Var i -> a i
    | Neg e' -> ( match eval e' a with True -> False | _ -> True)
    | And (e1, e2) -> ( match eval e1 a with False -> False | _ -> eval e2 a)
    | Or (e1, e2) -> ( match eval e2 a with True -> True | _ -> eval e2 a)
    | Imply (e1, e2) -> ( match eval e1 a with False -> True | _ -> eval e2 a)

  type exp' =
    | Var : int -> exp'
    | Neg : exp' -> exp'
    | Or : exp' * exp' -> exp'

  let dne (e : exp') : exp' = match e with Neg (Neg e') -> e' | _ -> e

  let rec desugar (e : exp) : exp' =
    let r e = dne (desugar e) in
    match e with
    | Var i -> Var i
    | Neg e' -> r e'
    | And (e1, e2) ->
        (* e1 && e2 <==> - (-e1 || -e2) *)
        Neg (Or (dne (Neg (desugar e1)), dne (Neg (desugar e2))))
    | Or (e1, e2) -> Or (desugar e1, desugar e2)
    | Imply (e1, e2) ->
        (* e1 ==> e2 <==> -e1 \/ e2 *)
        Or (dne (Neg (desugar e1)), desugar e2)
end

module Calc = struct
  type t = Const of int | Add of t * t | Mul of t * t

  let rec eval (p : t) : int =
    match p with
    | Const n -> n
    | Add (p, q) -> eval p + eval q
    | Mul (p, q) -> eval p * eval q
end

module Arith = struct
  type t = Const of int | X | Add of t * t | Mul of t * t | Compose of t * t

  let rec eval (n : int) : t -> int = function
    | Const m -> m
    | X -> n
    | Add (p, q) -> eval n p + eval n q
    | Mul (p, q) -> eval n p * eval n q
    | Compose (p, q) -> eval (eval n p) q

  (* let rec derivative : t -> t = function
     | Const q -> Const 0
     | X -> Const 1
     | Add (p, q) -> Add (derivative p, derivative q)
     | Mul (p, q) -> Add (Mul (derivative p, q), Mul (p, derivative q))
     | Compose (p, q) -> Mul (Compose (derivative p, q), derivative q) *)

  let desugar (f : t) : t =
    let rec helper (x : t) : t -> t = function
      | Const q -> Const q
      | X -> x
      | Add (p, q) -> Add (helper p x, helper q x)
      | Mul (p, q) -> Mul (helper p x, helper q x)
      | Compose (p, q) -> helper q (helper p x)
    in
    helper f X

  let rec simplify (f : t) : t =
    match f with
    | Const n -> Const n
    | X -> X
    | Add (p, q) -> (
        match (simplify p, simplify q) with
        | Const m, Const n -> Const (m + n)
        | Const 0, q' -> q'
        | p', Const 0 -> p'
        | p', q' -> Add (p', q'))
    | Mul (p, q) -> (
        match (simplify p, simplify q) with
        | Const m, Const n -> Const (m * n)
        | Const 1, q' -> q'
        | p', Const 1 -> p'
        | _, Const 0 -> Const 0
        | Const 0, _ -> Const 0
        | p', q' -> Mul (p', q'))
    | Compose (p, q) -> (
        let q' = simplify q in
        match simplify p with
        | Const n -> Const (eval n q')
        | X -> q'
        | p' -> Compose (p', q'))
end

(* bonus *)
module Polynomial = struct
  type t = int list

  let is_normal (f : t) : bool =
    let rec helper f last : bool =
      match f with [] -> true | f0 :: f' -> f0 = last && helper f' last
    in
    match List.rev f with [] -> true | last :: f' -> helper f' last

  let zero : t = []
  let one : t = [ 1 ]
  let x : t = [ 0; 1 ]

  let rec eval (f : t) (n : int) : int =
    match f with [] -> 0 | f0 :: f' -> f0 + (n * eval f' n)

  let rec to_arith (f : t) : Arith.t =
    match f with
    | [] -> Const 0
    | f0 :: f' -> Add (Const f0, Mul (X, to_arith f))

  (*
     let rec repeat n x = if n <= 0 then [] else x :: repeat (n-1) x
     let rec zipWithPad xs ys f z =
     match xs, ys with
     | [], [] -> []
     | [], _  -> repeat (List.length ys) z
     | _,  []  -> repeat (List.length xs) z
     | x::xs', y::ys' -> f x y :: zipWithPad xs' ys' f z *)

  let rec add (f : t) (g : t) : t =
    match (f, g) with
    | [], [] -> []
    | [], _ -> g
    | _, [] -> f
    | f0 :: f', g0 :: g' -> (f0 + g0) :: add f' g'

  let scale (k : int) (f : t) : t = List.map (( * ) k) f
  let neg (f : t) : t = scale (-1) f
  let sub (f : t) (g : t) : t = add f (neg g)
  let sum = List.fold_left ( + ) 0

  let rec mul (f : t) (g : t) : t =
    match (f, g) with
    | [], _ -> []
    | _, [] -> []
    | f0 :: f', g0 :: g' ->
        (f0 * g0) :: add (scale f0 g') (add (scale g0 f') (0 :: mul f g))

  let rec from_arith (f : Arith.t) : t =
    match f with
    | Const c -> [ c ]
    | X -> x
    | Add (p, q) -> add (from_arith p) (from_arith q)
    | Mul (p, q) -> mul (from_arith p) (from_arith q)
    | Compose _ -> from_arith (Arith.desugar f)
end
