let () = Random.self_init ()
let size = 1_000_000
let input_add = Array.init size (fun _ -> Random.int size)
let input_remove = Array.init size (fun _ -> Random.int size)

module type S = sig
  type elt = int
  type t

  val empty : t
  val add : elt -> t -> t
  val remove : elt -> t -> t
  val mem : elt -> t -> bool
  val to_seq : t -> elt Seq.t
end

let test (module Set : S) =
  let t = Set.empty in
  let t = Array.fold_left (fun t x -> Set.add x t) t input_add in
  Array.iter (fun x -> assert (Set.mem x t)) input_add ;
  let t = Array.fold_left (fun t x -> Set.remove x t) t input_remove in
  Array.iter (fun x -> assert (not (Set.mem x t))) input_remove ;
  let seq = Set.to_seq t in
  Seq.iter (fun x -> assert (Set.mem x t)) seq ;
  List.of_seq seq

let () =
  let stdlib = test (module Set.Make (Int)) in
  assert (List.length stdlib > 0) ;
  assert (List.length stdlib < size) ;
  let redblack = test (module Redblack.Make (Int)) in
  assert (stdlib = redblack) ;
  let avl = test (module Avl.Make (Int)) in
  assert (stdlib = avl) ;
  let b23 = test (module B23.Make (Int)) in
  assert (stdlib = b23) ;
  let b234 = test (module B234.Make (Int)) in
  assert (stdlib = b234) ;
  ()
