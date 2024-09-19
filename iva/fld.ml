open Base

module type S0 = sig
  type t [@@deriving sexp]

  val zero : t
  val one : t
  val add : t -> t -> t
  val neg : t -> t
  val mul : t -> t -> t
  val inv : t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : t Fmt.t
end

module type S = sig
  include S0

  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( ~- ) : t -> t
  val ( - ) : t -> t -> t
  val ( ~/ ) : t -> t
  val ( / ) : t -> t -> t
  val ( ** ) : t -> Z.t -> t

  include Comparable.S with type t := t
end

module Make (F : S0) = struct
  include F
  include Comparable.Make (F)

  let ( + ) = add
  let ( ~- ) = neg
  let ( * ) = mul
  let ( ~/ ) = inv
  let ( - ) a b = a + -b
  let ( / ) a b = a * ~/b

  let rec pow f n =
    if Z.(equal n zero) then one
    else if Z.(equal n one) then f
    else
      let f2 = f * f in
      let n2 = Z.shift_right n 1 in
      let r = pow f2 n2 in
      if Z.(equal (n land one) zero) then r else r * f

  let ( ** ) = pow
end

module Z = struct
  include Z

  let pp = Z.pp_print
  let sexp_of_t x = x |> Z.to_string |> [%sexp_of: string]
  let t_of_sexp x = x |> [%of_sexp: string] |> Z.of_string

  include Z.Compare

  let rec ext_euclid (a : t) (b : t) : t * (t * t) =
    let d, (m, n) =
      if b = zero then (a, (one, zero))
      else
        let q, r = ediv_rem a b in
        let d, (m, n) = ext_euclid b r in
        (* a = qb + r *)
        (* r = a - qb *)
        (* mb + nr = gcd *)
        (* RHS = mb + n(a-qb) = mb + na - nqb = (m-qn)b + na *)
        (d, (n, m - (q * n)))
    in
    assert ((m * a) + (n * b) = d);
    (d, (m, n))
end

module Q0 = struct
  include Q

  let pp = Q.pp_print
  let sexp_of_t ({ num; den } : t) = [%sexp_of: Z.t * Z.t] (num, den)

  let t_of_sexp s =
    let num, den = [%of_sexp: Z.t * Z.t] s in
    Q.make num den
end

module Fin0 (F : Ff_sig.PRIME_WITH_ROOT_OF_UNITY) = struct
  include F

  let t_of_sexp s = s |> Z.t_of_sexp |> of_z
  let sexp_of_t x = x |> to_z |> Z.sexp_of_t
  let neg = F.( - )
  let inv = F.inverse_exn
  let equal = F.eq
  let compare f1 f2 = Z.compare (to_z f1) (to_z f2)

  let pp ppf f =
    let z = to_z f in
    let z' = Z.(if z <= F.order / of_int 2 then z else z - F.order) in
    Z.pp ppf z'
end

module Q = struct
  include Q0
  include Make (Q0)
end

module Fin (M : sig
  val modulus : Z.t
end) =
struct
  module F = Ff.MakeFp (struct
    let prime_order = M.modulus
  end)

  include F
  include Make (Fin0 (F))
end
