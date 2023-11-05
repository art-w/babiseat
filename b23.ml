module Make (Elt : Set.OrderedType) : sig
  type elt = Elt.t
  type t

  val empty : t
  val add : elt -> t -> t
  val remove : elt -> t -> t
  val mem : elt -> t -> bool
  val to_seq : t -> elt Seq.t
end = struct
  type elt = Elt.t

  (* Invariants *)

  type zero = ZERO [@@warning "-unused-constructor"]
  type 'a succ = SUCC of 'a [@@warning "-unused-constructor"]

  type 'height tree =
    | Leaf : zero tree
    | B2 : 'h tree * elt * 'h tree -> 'h succ tree
    | B3 : 'h tree * elt * 'h tree * elt * 'h tree -> 'h succ tree

  type t = T : _ tree -> t [@@unboxed]

  let empty = T Leaf

  (* Queries *)

  let rec mem : type h. elt -> h tree -> bool =
    fun elt -> function
    | Leaf -> false
    | B2 (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> true
      | cmp when cmp < 0 -> mem elt left
      | _ -> mem elt right
    end
    | B3 (left, pivot_left, center, pivot_right, right) -> begin
      match Elt.compare elt pivot_left with
      | 0 -> true
      | c when c < 0 -> mem elt left
      | _ -> begin
        match Elt.compare elt pivot_right with
        | 0 -> true
        | cmp when cmp < 0 -> mem elt center
        | _ -> mem elt right
      end
    end

  let mem elt (T t) = mem elt t

  let rec to_seq : type h. h tree -> elt Seq.t = function
    | Leaf -> Seq.empty
    | B2 (left, pivot, right) -> Seq.append (to_seq left) @@ Seq.cons pivot (to_seq right)
    | B3 (left, pivot_left, center, pivot_right, right) ->
      Seq.append (to_seq left)
      @@ Seq.cons pivot_left
      @@ Seq.append (to_seq center)
      @@ Seq.cons pivot_right (to_seq right)

  let to_seq (T t) = to_seq t

  (* Add *)

  type 'height add_result =
    | Ok : 'h tree -> 'h add_result
    | Overflow : 'h tree * elt * 'h tree -> 'h add_result

  let rec add : type h. elt -> h tree -> h add_result =
    fun elt tree ->
    match tree with
    | Leaf -> Overflow (Leaf, elt, Leaf)
    | B2 (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> Ok tree
      | cmp when cmp < 0 -> begin
        match add elt left with
        | Ok left -> Ok (B2 (left, pivot, right))
        | Overflow (a, b, c) -> Ok (B3 (a, b, c, pivot, right))
      end
      | _ -> begin
        match add elt right with
        | Ok right -> Ok (B2 (left, pivot, right))
        | Overflow (a, b, c) -> Ok (B3 (left, pivot, a, b, c))
      end
    end
    | B3 (left, pivot_left, center, pivot_right, right) -> begin
      match Elt.compare elt pivot_left with
      | 0 -> Ok tree
      | cmp when cmp < 0 -> begin
        match add elt left with
        | Ok left -> Ok (B3 (left, pivot_left, center, pivot_right, right))
        | Overflow (a, b, c) ->
          Overflow (B2 (a, b, c), pivot_left, B2 (center, pivot_right, right))
      end
      | _ -> begin
        match Elt.compare elt pivot_right with
        | 0 -> Ok tree
        | cmp when cmp < 0 -> begin
          match add elt center with
          | Ok center -> Ok (B3 (left, pivot_left, center, pivot_right, right))
          | Overflow (a, b, c) ->
            Overflow (B2 (left, pivot_left, a), b, B2 (c, pivot_right, right))
        end
        | _ -> begin
          match add elt right with
          | Ok right -> Ok (B3 (left, pivot_left, center, pivot_right, right))
          | Overflow (a, b, c) ->
            Overflow (B2 (left, pivot_left, center), pivot_right, B2 (a, b, c))
        end
      end
    end

  let add elt (T t) =
    match add elt t with
    | Ok t -> T t
    | Overflow (a, b, c) -> T (B2 (a, b, c))

  (* Remove *)

  type 'height remove_result =
    | Uk : 'height tree -> 'height remove_result
    | Underflow : 'height tree -> 'height succ remove_result

  type 'height uncons_result =
    | Is_empty : zero uncons_result
    | Pop : elt * 'height remove_result -> 'height uncons_result

  let b2_left : type h. h remove_result -> elt -> h tree -> h succ remove_result =
    fun left pivot right ->
    match left, pivot, right with
    | Uk left, pivot, right -> Uk (B2 (left, pivot, right))
    | Underflow a, b, B2 (c, d, e) -> Underflow (B3 (a, b, c, d, e))
    | Underflow a, b, B3 (c, d, e, f, g) -> Uk (B2 (B2 (a, b, c), d, B2 (e, f, g)))

  let b3_left
    : type h. h remove_result -> elt -> h tree -> elt -> h tree -> h succ remove_result
    =
    fun left pivot_left center pivot_right right ->
    match left, pivot_left, center, pivot_right, right with
    | Uk left, pivot_left, center, pivot_right, right ->
      Uk (B3 (left, pivot_left, center, pivot_right, right))
    | Underflow a, b, B2 (c, d, e), f, g -> Uk (B2 (B3 (a, b, c, d, e), f, g))
    | Underflow a, b, B3 (c, d, e, f, g), h, i ->
      Uk (B3 (B2 (a, b, c), d, B2 (e, f, g), h, i))

  let rec uncons : type h. h tree -> h uncons_result = function
    | Leaf -> Is_empty
    | B2 (left, pivot, right) -> begin
      match uncons left with
      | Is_empty -> Pop (pivot, Underflow right)
      | Pop (elt, left) -> Pop (elt, b2_left left pivot right)
    end
    | B3 (left, pivot_left, center, pivot_right, right) -> begin
      match uncons left with
      | Is_empty -> Pop (pivot_left, Uk (B2 (center, pivot_right, right)))
      | Pop (elt, left) -> Pop (elt, b3_left left pivot_left center pivot_right right)
    end

  let b2_right : type h. h tree -> elt -> h remove_result -> h succ remove_result =
    fun left pivot right ->
    match left, pivot, right with
    | left, pivot, Uk right -> Uk (B2 (left, pivot, right))
    | B2 (a, b, c), d, Underflow e -> Underflow (B3 (a, b, c, d, e))
    | B3 (a, b, c, d, e), f, Underflow g -> Uk (B2 (B2 (a, b, c), d, B2 (e, f, g)))

  let b3_center
    : type h. h tree -> elt -> h remove_result -> elt -> h tree -> h succ remove_result
    =
    fun left pivot_left center pivot_right right ->
    match left, pivot_left, center, pivot_right, right with
    | left, pivot_left, Uk center, pivot_right, right ->
      Uk (B3 (left, pivot_left, center, pivot_right, right))
    | B2 (a, b, c), d, Underflow e, f, g -> Uk (B2 (B3 (a, b, c, d, e), f, g))
    | B3 (a, b, c, d, e), f, Underflow g, h, i ->
      Uk (B3 (B2 (a, b, c), d, B2 (e, f, g), h, i))

  let b3_right
    : type h. h tree -> elt -> h tree -> elt -> h remove_result -> h succ remove_result
    =
    fun left pivot_left center pivot_right right ->
    match left, pivot_left, center, pivot_right, right with
    | left, pivot_left, center, pivot_right, Uk right ->
      Uk (B3 (left, pivot_left, center, pivot_right, right))
    | a, b, B2 (c, d, e), f, Underflow g -> Uk (B2 (a, b, B3 (c, d, e, f, g)))
    | a, b, B3 (c, d, e, f, g), h, Underflow i ->
      Uk (B3 (a, b, B2 (c, d, e), f, B2 (g, h, i)))

  let rec remove : type h. elt -> h tree -> h remove_result =
    fun elt -> function
    | Leaf -> Uk Leaf
    | B2 (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> begin
        match uncons right with
        | Is_empty ->
          let Leaf = left in
          Underflow Leaf
        | Pop (new_pivot, right) -> b2_right left new_pivot right
      end
      | cmp when cmp < 0 -> b2_left (remove elt left) pivot right
      | _ -> b2_right left pivot (remove elt right)
    end
    | B3 (left, pivot_left, center, pivot_right, right) -> begin
      match Elt.compare elt pivot_left with
      | 0 -> begin
        match uncons center with
        | Is_empty ->
          let Leaf = left in
          let Leaf = right in
          Uk (B2 (Leaf, pivot_right, Leaf))
        | Pop (pivot_left, center) -> b3_center left pivot_left center pivot_right right
      end
      | cmp when cmp < 0 -> b3_left (remove elt left) pivot_left center pivot_right right
      | _ -> begin
        match Elt.compare elt pivot_right with
        | 0 -> begin
          match uncons right with
          | Is_empty ->
            let Leaf = left in
            let Leaf = right in
            Uk (B2 (Leaf, pivot_left, Leaf))
          | Pop (pivot_right, right) -> b3_right left pivot_left center pivot_right right
        end
        | cmp when cmp < 0 ->
          b3_center left pivot_left (remove elt center) pivot_right right
        | _ -> b3_right left pivot_left center pivot_right (remove elt right)
      end
    end

  let remove elt (T t) =
    match remove elt t with
    | Uk t -> T t
    | Underflow t -> T t
end
