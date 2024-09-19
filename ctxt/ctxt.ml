open Core

type e = Int of int | Plus of e * e [@@deriving show, eq]
type value = VInt of int [@@deriving show, eq]

let to_value = function Int n -> Some (VInt n) | _ -> None
let of_value = function VInt n -> Int n

type ctxt = Hole | CPlus1 of ctxt * e | CPlus2 of value * ctxt
[@@deriving show, eq]

let rec unify (c : ctxt) (e : e) : e option =
  match (c, e) with
  | Hole, _ -> Some e
  | CPlus1 (c', e2), Plus (e1, e2') when equal_e e2 e2' ->
      Option.map (unify c' e1) ~f:(fun e1' -> Plus (e1', e2'))
  | CPlus2 (v, c'), Plus (e1, e2) when equal_e (of_value v) e1 ->
      Option.map (unify c' e2) ~f:(fun e2' -> Plus (e1, e2'))
  | _ -> None

let rec inst (e : e) : ctxt -> e = function
  | Hole -> e
  | CPlus1 (c, e2) -> Plus (inst e c, e2)
  | CPlus2 (v, c) -> Plus (of_value v, inst e c)

let rec compose (c : ctxt) : ctxt -> ctxt = function
  | Hole -> c
  | CPlus1 (c', e2) -> CPlus1 (compose c c', e2)
  | CPlus2 (e1, c') -> CPlus2 (e1, compose c c')

(* let rec build_ctxt : e -> ctxt option = function
   | Int _ ->
       None
   | Plus (e1, e2) ->
       match to_value e1 with
       | None ->
         Some (CPlus1 (Option.value_exn (build_ctxt e1), e2))
       else Option.map (build_ctxt e2) ~f:(fun c -> CPlus2 (e1, c)) *)

let rec focus : e -> (e * ctxt) option = function
  | Plus (e1, e2) -> (
      match to_value e1 with
      | None -> Option.map (focus e1) ~f:(fun (e1', c) -> (e1', CPlus1 (c, e2)))
      | Some v ->
          Option.map (focus e2) ~f:(fun (e2', c) -> (e2', CPlus2 (v, c))))
  | _ -> None

let step_instruction : e -> e option = function
  | Plus (Int m, Int n) -> Some (Int (m + n))
  | _ -> None

let step (e : e) : e option =
  match focus e with
  | None -> None
  | Some (e', c) -> step_instruction (inst e' c)

let rec steps e : e = match step e with None -> e | Some e' -> steps e'

module Fast = struct
  let rec decompose : e -> e * ctxt list = function
    | Int _ as e -> (e, [])
    | Plus (e1, e2) -> (
        match to_value e1 with
        | None ->
            let e, c = decompose e1 in
            (e, c @ [ CPlus1 (Hole, e2) ])
        | Some v ->
            let e, c = decompose e2 in
            (e, c @ [ CPlus2 (v, Hole) ]))

  let steps : e -> e =
    let rec aux (e, c) : e =
      match c with
      | [] -> (
          match step_instruction e with
          | None -> e
          | Some e' -> aux (decompose e'))
      | c1 :: c' -> aux (inst e c1, c')
    in
    Fn.compose aux decompose
end
