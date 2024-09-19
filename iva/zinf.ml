(* module Zinf = struct
     exception Undefined

     type t = Inf | NInf | Fin of Z.t

     let show = function Fin n -> Z.to_string n | Inf -> "+∞" | NInf -> "-∞"

     let add (m : t) (n : t) : t =
       match (m, n) with
       | Inf, NInf | NInf, Inf ->
           raise Undefined
       | Inf, _ | _, Inf ->
           Inf
       | NInf, _ | _, NInf ->
           NInf
       | Fin m, Fin n ->
           Fin Z.(m + n)
     let
   end *)
