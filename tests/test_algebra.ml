(* module Z_tests = struct
     open Iva.Field.Z

     let test_div'_raises () =
       Alcotest.check_raises "div by 0" Division_by_zero (fun () ->
           ignore (div' 0 0) ) ;
       Alcotest.check_raises "div by neg" Out_of_range (fun () ->
           ignore (div' 0 (-1)) ) ;
       Alcotest.check_raises "div by neg" Out_of_range (fun () ->
           ignore (div' 0 (-1)) )
   end *)
open Core

module Test_finite_field = struct
  open Alcotest
  module F = Iva.Algebra.F_13

  let t = testable F.pp F.equal
  let pp = Fn.flip F.pp

  let test_add () =
    List.iter
      ~f:(fun (l, r, exp) ->
        check' t
          ~msg:Fmt.(str "%a + %a = %a" int l int r int exp)
          ~expected:(Z.of_int exp)
          ~actual:F.(Z.of_int l + Z.of_int r))
      [ (0, 0, 0); (0, 1, 1); (1, 0, 1); (1, 3, 4); (6, 7, 0); (9, 10, 6) ]

  let test_mul () =
    List.iter
      ~f:(fun (l, r, exp) ->
        check' t
          ~msg:Fmt.(str "%a + %a = %a" int l int r int exp)
          ~expected:(Z.of_int exp)
          ~actual:F.(Z.of_int l * Z.of_int r))
      [ (0, 1, 0); (3, 0, 0); (3, 4, 12); (5, 5, 12); (10, 10, 9) ]

  let test_inv () =
    List.iter
      ~f:(fun l ->
        check' t
          ~msg:Fmt.(str "1/%a * %a = 1" Z.pp_print l Z.pp_print l)
          ~expected:(Z.of_int 1)
          ~actual:F.(inv l * l))
      (Util.range ~lo:0 ~hi:14)

  let suite =
    ( "finite field",
      [
        Alcotest.test_case "add" `Quick test_add;
        Alcotest.test_case "mul" `Quick test_mul;
        Alcotest.test_case "inv" `Quick test_inv;
      ] )
end

let suite = [ Test_finite_field.suite ]
