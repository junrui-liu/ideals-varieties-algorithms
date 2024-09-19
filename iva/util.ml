open Base

let ( <.> ) = Fn.compose

(** Create an optional value if the predicate holds *)
let create_option_if (x : 'a) ~(f : 'a -> bool) : 'a option =
  if f x then Some x else None

let range ?(lo : int = 0) ~(hi : int) =
  List.init lo ~f:(fun i -> Z.(of_int i + of_int Int.(hi - lo)))

let number ?(start : int = 0) (xs : 'a list) =
  List.zip_exn (List.init (List.length xs) ~f:(fun i -> i + start)) xs
  |> List.map ~f:(fun (i, x) -> (i + start, x))

let product (xs : 'a list) (ys : 'b list) : ('a * 'b) list =
  List.cartesian_product xs ys
