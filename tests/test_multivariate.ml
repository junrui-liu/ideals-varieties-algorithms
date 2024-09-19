open Core
open Alcotest
module F = Iva.Algebra.FQ
module M = Iva.Multivariate.Coeff (F)
open M

let t = testable M.pp M.equal
let t_mono = testable M.pp_mdegree M.equal_mdegree
let c = Fn.compose const Q.of_int

let test_order (module O : Iva.Multivariate.Order.S) =
  let t_sign = testable Base.Sign.pp Base.Sign.equal in
  List.iter ~f:(fun (l, r, exp) ->
      let act = Int.sign (O.compare l r) in
      check' t_sign
        ~msg:
          Fmt.(
            str "order %a < %a : %a =? %a" M.pp_mdegree l M.pp_mdegree r
              Base.Sign.pp act Base.Sign.pp exp)
        ~expected:exp ~actual:act)

let test_lex () =
  test_order
    (module Iva.Multivariate.Order.Lex)
    Base.Sign.
      [
        ([ 0 ], [ 0 ], Zero);
        ([ 0 ], [ 1 ], Neg);
        ([ 1 ], [ 0 ], Pos);
        ([ 1 ], [ 1 ], Zero);
        ([ 0; 0 ], [ 0; 0 ], Zero);
        ([ 0; 0 ], [ 0; 1 ], Neg);
        ([ 0; 0 ], [ 1; 0 ], Neg);
        ([ 0; 0 ], [ 1; 1 ], Neg);
        ([ 0; 1 ], [ 0; 0 ], Pos);
        ([ 0; 1 ], [ 0; 1 ], Zero);
        ([ 0; 1 ], [ 1; 0 ], Neg);
        ([ 0; 1 ], [ 1; 1 ], Neg);
        ([ 1; 0 ], [ 0; 0 ], Pos);
        ([ 1; 0 ], [ 0; 1 ], Pos);
        ([ 1; 0 ], [ 1; 0 ], Zero);
        ([ 1; 0 ], [ 1; 1 ], Neg);
        ([ 1; 1 ], [ 0; 0 ], Pos);
        ([ 1; 1 ], [ 0; 1 ], Pos);
        ([ 1; 1 ], [ 1; 0 ], Pos);
        ([ 1; 1 ], [ 1; 1 ], Zero);
        ([ 1; 2; 0 ], [ 0; 3; 4 ], Pos);
        ([ 0; 3; 4 ], [ 1; 2; 0 ], Neg);
        ([ 3; 2; 4 ], [ 3; 2; 1 ], Pos);
        ([ 3; 2; 1 ], [ 3; 2; 4 ], Neg);
      ]

let test_grlex () =
  test_order
    (module Iva.Multivariate.Order.GrLex)
    [
      ([ 1; 2; 3 ], [ 3; 2; 0 ], Pos);
      ([ 3; 2; 0 ], [ 1; 2; 3 ], Neg);
      ([ 1; 2; 4 ], [ 1; 1; 5 ], Pos);
      ([ 1; 1; 5 ], [ 1; 2; 4 ], Neg);
    ]

let test_grevlex () =
  test_order
    (module Iva.Multivariate.Order.GrevLex)
    [ ([ 4; 7; 1 ], [ 4; 2; 3 ], Pos); ([ 1; 5; 2 ], [ 4; 1; 3 ], Pos) ]

let test_sort () =
  let f =
    (c 4 * x * (y ^ 2) * z)
    + (c 4 * (z ^ 2))
    - (c 5 * (x ^ 3))
    + (c 7 * (x ^ 2) * (z ^ 2))
  in
  (* Fmt.pr "f = %a\n" M.pp f ; *)
  let i = Q.of_int in
  let cases =
    [
      ( "lex",
        M.lex,
        [
          ([ 3 ], i (-5));
          ([ 2; 0; 2 ], i 7);
          ([ 1; 2; 1 ], i 4);
          ([ 0; 0; 2 ], i 4);
        ] );
      ( "grlex",
        M.grlex,
        [
          ([ 2; 0; 2 ], i 7);
          ([ 1; 2; 1 ], i 4);
          ([ 3 ], i (-5));
          ([ 0; 0; 2 ], i 4);
        ] );
      ( "grevlex",
        M.grevlex,
        [
          ([ 1; 2; 1 ], i 4);
          ([ 2; 0; 2 ], i 7);
          ([ 3 ], i (-5));
          ([ 0; 0; 2 ], i 4);
        ] );
    ]
  in
  let pp = Util.pp_of_show [%derive.show: (mdegree * F.t) list] in
  let t_coeff = testable pp [%derive.eq: (mdegree * F.t) list] in
  List.iter cases ~f:(fun (name, sort, exp) ->
      let act = sort f in
      check' t_coeff
        ~msg:(Fmt.str "%s(%a) = %a =? %a" name M.pp f pp act pp exp)
        ~expected:exp ~actual:act)

let test_add () =
  List.iter
    ~f:(fun (l, r, exp) ->
      (* Fmt.pr "%a + %a = %a =? %a\n" M.pp_debug l M.pp_debug r M.pp_debug (M.(l+r)) M.pp_debug exp ; *)
      check' t
        ~msg:Fmt.(str "%a + %a = %a" M.pp l M.pp r M.pp exp)
        ~expected:exp
        ~actual:M.(l + r))
    [
      (xi 0, -xi 0, c 0);
      (xi 0, xi 0, c 2 * xi 0);
      (xi 0, xi 1, xi 0 + xi 1);
      (xi 0 + xi 1, xi 1 - xi 0 - xi 2, (c 2 * xi 1) - xi 2);
    ]

let test_mul () =
  List.iter
    ~f:(fun (l, r, exp) ->
      (* Fmt.pr "[debug] %a * %a = %a =? %a\n" M.pp_debug l M.pp_debug r M.pp_debug
         M.(l * r)
         M.pp_debug exp ; *)
      check' t
        ~msg:Fmt.(str "%a * %a = %a" M.pp l M.pp r M.pp exp)
        ~expected:exp
        ~actual:M.(l * r))
    [ (xi 0, -xi 0, -(xi 0 ^ 2)); (xi 0 * xi 1, xi 2, xi 0 * xi 1 * xi 2) ]

let test_div () =
  let module F = Iva.Algebra.FQ in
  let module M = Iva.Multivariate.Coeff (F) in
  M.(
    let c = Fn.compose const Q.of_int in
    let input =
      [
        (let f = (x * (y ^ 2)) + c 1
         and f0 = (x * y) + c 1
         and f1 = y + c 1
         and q0 = y
         and q1 = -c 1
         and r = c 2 in
         (f, [ f0; f1 ], ([ q0; q1 ], r)));
        (let f = ((x ^ 2) * y) + (x * (y ^ 2)) + (y ^ 2) in
         let f0 = (x * y) - c 1 in
         let f1 = (y ^ 2) - c 1 in
         let q0 = x + y in
         let q1 = c 1 in
         let r = x + y + c 1 in
         (f, [ f0; f1 ], ([ q0; q1 ], r)));
      ]
    in
    let pp = Util.pp_of_show [%derive.show: t list * t] in
    let t = testable pp [%derive.eq: t list * t] in
    List.iter input ~f:(fun (f, fs, (qs, r)) ->
        let qs', r' = div f fs in
        check' t
          ~msg:
            (Fmt.str "%a / %a = %a =? %a" M.pp f (Fmt.list M.pp) fs pp (qs, r)
               pp (qs', r'))
          ~expected:(qs, r) ~actual:(qs', r');
        let mul =
          List.zip_exn fs qs'
          |> List.fold ~init:r' ~f:(fun acc (f, q) -> acc + (f * q))
        in
        check' (testable M.pp M.( = ))
          ~msg:
            (Fmt.str "%a . %a + %a = %a" (Fmt.list M.pp) qs' (Fmt.list M.pp) fs
               M.pp r' M.pp f)
          ~expected:f ~actual:mul))

let suite =
  [
    ( "multivariate",
      [
        Alcotest.test_case "lex" `Quick test_lex;
        Alcotest.test_case "grlex" `Quick test_grlex;
        Alcotest.test_case "grevlex" `Quick test_grevlex;
        Alcotest.test_case "add" `Quick test_add;
        Alcotest.test_case "mul" `Quick test_mul;
        Alcotest.test_case "sort" `Quick test_sort;
        Alcotest.test_case "div" `Quick test_div;
      ] );
  ]
