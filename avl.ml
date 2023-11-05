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
    | Eq : 'h tree * elt * 'h tree -> 'h succ tree
    | Left : 'h succ tree * elt * 'h tree -> 'h succ succ tree
    | Right : 'h tree * elt * 'h succ tree -> 'h succ succ tree

  type t = T : _ tree -> t [@@unboxed]

  let empty = T Leaf

  (* Queries *)

  let rec mem : type h. elt -> h tree -> bool =
    fun elt -> function
    | Leaf -> false
    | Eq (left, pivot, right) -> mem_bin elt left pivot right
    | Left (left, pivot, right) -> mem_bin elt left pivot right
    | Right (left, pivot, right) -> mem_bin elt left pivot right

  and mem_bin : type h1 h2. elt -> h1 tree -> elt -> h2 tree -> bool =
    fun elt left pivot right ->
    match Elt.compare elt pivot with
    | 0 -> true
    | cmp when cmp < 0 -> mem elt left
    | _ -> mem elt right

  let mem elt (T t) = mem elt t

  let rec to_seq : type h. h tree -> elt Seq.t = function
    | Leaf -> Seq.empty
    | Eq (left, pivot, right) -> Seq.append (to_seq left) @@ Seq.cons pivot (to_seq right)
    | Left (left, pivot, right) ->
      Seq.append (to_seq left) @@ Seq.cons pivot (to_seq right)
    | Right (left, pivot, right) ->
      Seq.append (to_seq left) @@ Seq.cons pivot (to_seq right)

  let to_seq (T t) = to_seq t

  (* Add *)

  type 'height add_result =
    | Ok : 'h tree -> 'h add_result
    | Overflow_single : elt -> zero add_result
    | Overflow_left : 'h succ tree * elt * 'h tree -> 'h succ add_result
    | Overflow_right : 'h tree * elt * 'h succ tree -> 'h succ add_result

  let single x = Eq (Leaf, x, Leaf)

  let rec add : type h. elt -> h tree -> h add_result =
    fun elt tree ->
    match tree with
    | Leaf -> Overflow_single elt
    | Eq (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> Ok tree
      | cmp when cmp < 0 -> begin
        match add elt left with
        | Ok left -> Ok (Eq (left, pivot, right))
        | Overflow_single left -> Overflow_left (single left, pivot, right)
        | Overflow_left (a, b, c) -> Overflow_left (Left (a, b, c), pivot, right)
        | Overflow_right (a, b, c) -> Overflow_left (Right (a, b, c), pivot, right)
      end
      | _ -> begin
        match add elt right with
        | Ok right -> Ok (Eq (left, pivot, right))
        | Overflow_single right -> Overflow_right (left, pivot, single right)
        | Overflow_left (a, b, c) -> Overflow_right (left, pivot, Left (a, b, c))
        | Overflow_right (a, b, c) -> Overflow_right (left, pivot, Right (a, b, c))
      end
    end
    | Left (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> Ok tree
      | cmp when cmp < 0 -> begin
        match add elt left with
        | Ok left -> Ok (Left (left, pivot, right))
        | Overflow_left (a, b, c) -> Ok (Eq (a, b, Eq (c, pivot, right)))
        | Overflow_right (a, b, Eq (c, d, e)) ->
          Ok (Eq (Eq (a, b, c), d, Eq (e, pivot, right)))
        | Overflow_right (a, b, Left (c, d, e)) ->
          Ok (Eq (Eq (a, b, c), d, Right (e, pivot, right)))
        | Overflow_right (a, b, Right (c, d, e)) ->
          Ok (Eq (Left (a, b, c), d, Eq (e, pivot, right)))
      end
      | _ -> begin
        match add elt right with
        | Ok right -> Ok (Left (left, pivot, right))
        | Overflow_single right -> Ok (Eq (left, pivot, single right))
        | Overflow_left (a, b, c) -> Ok (Eq (left, pivot, Left (a, b, c)))
        | Overflow_right (a, b, c) -> Ok (Eq (left, pivot, Right (a, b, c)))
      end
    end
    | Right (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> Ok tree
      | cmp when cmp > 0 -> begin
        match add elt right with
        | Ok right -> Ok (Right (left, pivot, right))
        | Overflow_right (a, b, c) -> Ok (Eq (Eq (left, pivot, a), b, c))
        | Overflow_left (Eq (a, b, c), d, e) ->
          Ok (Eq (Eq (left, pivot, a), b, Eq (c, d, e)))
        | Overflow_left (Left (a, b, c), d, e) ->
          Ok (Eq (Eq (left, pivot, a), b, Right (c, d, e)))
        | Overflow_left (Right (a, b, c), d, e) ->
          Ok (Eq (Left (left, pivot, a), b, Eq (c, d, e)))
      end
      | _ -> begin
        match add elt left with
        | Ok left -> Ok (Right (left, pivot, right))
        | Overflow_single left -> Ok (Eq (single left, pivot, right))
        | Overflow_left (a, b, c) -> Ok (Eq (Left (a, b, c), pivot, right))
        | Overflow_right (a, b, c) -> Ok (Eq (Right (a, b, c), pivot, right))
      end
    end

  let add elt (T t) =
    match add elt t with
    | Ok t -> T t
    | Overflow_single t -> T (single t)
    | Overflow_left (a, b, c) -> T (Left (a, b, c))
    | Overflow_right (a, b, c) -> T (Right (a, b, c))

  (* Remove *)

  type 'height remove_result =
    | Uk : 'height tree -> 'height remove_result
    | Underflow : 'h tree -> 'h succ remove_result

  let eq_left : type h. h remove_result -> elt -> h tree -> h succ remove_result =
    fun left pivot right ->
    match left with
    | Uk left -> Uk (Eq (left, pivot, right))
    | Underflow left -> Uk (Right (left, pivot, right))

  let left_left
    : type h. h succ remove_result -> elt -> h tree -> h succ succ remove_result
    =
    fun left pivot right ->
    match left with
    | Uk left -> Uk (Left (left, pivot, right))
    | Underflow left -> Underflow (Eq (left, pivot, right))

  type 'height uncons_result =
    | Is_empty : zero uncons_result
    | Pop : elt * 'height remove_result -> 'height uncons_result

  let right_left
    : type h. h remove_result -> elt -> h succ tree -> h succ succ remove_result
    =
    fun left pivot right ->
    match left, pivot, right with
    | Uk left, _, _ -> Uk (Right (left, pivot, right))
    | Underflow a, b, Eq (c, d, e) -> Uk (Left (Right (a, b, c), d, e))
    | Underflow a, b, Left (Eq (c, d, e), f, g) ->
      Underflow (Eq (Eq (a, b, c), d, Eq (e, f, g)))
    | Underflow a, b, Left (Left (c, d, e), f, g) ->
      Underflow (Eq (Eq (a, b, c), d, Right (e, f, g)))
    | Underflow a, b, Left (Right (c, d, e), f, g) ->
      Underflow (Eq (Left (a, b, c), d, Eq (e, f, g)))
    | Underflow a, b, Right (c, d, e) -> Underflow (Eq (Eq (a, b, c), d, e))

  let rec uncons : type h. h tree -> h uncons_result = function
    | Leaf -> Is_empty
    | Eq (left, pivot, right) -> begin
      match uncons left with
      | Is_empty ->
        let Leaf = right in
        Pop (pivot, Underflow Leaf)
      | Pop (elt, left) -> Pop (elt, eq_left left pivot right)
    end
    | Left (left, pivot, right) -> begin
      match uncons left with
      | Pop (elt, left) -> Pop (elt, left_left left pivot right)
    end
    | Right (left, pivot, right) -> begin
      match uncons left with
      | Is_empty -> Pop (pivot, Underflow right)
      | Pop (elt, left) -> Pop (elt, right_left left pivot right)
    end

  let eq_right : type h. h tree -> elt -> h remove_result -> h succ remove_result =
    fun left pivot right ->
    match right with
    | Uk right -> Uk (Eq (left, pivot, right))
    | Underflow right -> Uk (Left (left, pivot, right))

  let left_right
    : type h. h succ tree -> elt -> h remove_result -> h succ succ remove_result
    =
    fun left pivot right ->
    match left, pivot, right with
    | _, _, Uk right -> Uk (Left (left, pivot, right))
    | Eq (a, b, c), d, Underflow e -> Uk (Right (a, b, Left (c, d, e)))
    | Right (a, b, Eq (c, d, e)), f, Underflow g ->
      Underflow (Eq (Eq (a, b, c), d, Eq (e, f, g)))
    | Right (a, b, Left (c, d, e)), f, Underflow g ->
      Underflow (Eq (Eq (a, b, c), d, Right (e, f, g)))
    | Right (a, b, Right (c, d, e)), f, Underflow g ->
      Underflow (Eq (Left (a, b, c), d, Eq (e, f, g)))
    | Left (a, b, c), d, Underflow e -> Underflow (Eq (a, b, Eq (c, d, e)))

  let right_right
    : type h. h tree -> elt -> h succ remove_result -> h succ succ remove_result
    =
    fun left pivot right ->
    match right with
    | Uk right -> Uk (Right (left, pivot, right))
    | Underflow right -> Underflow (Eq (left, pivot, right))

  let rec remove : type h. elt -> h tree -> h remove_result =
    fun elt -> function
    | Leaf -> Uk Leaf
    | Eq (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> begin
        match uncons right with
        | Is_empty -> Underflow left
        | Pop (pivot, right) -> eq_right left pivot right
      end
      | cmp when cmp < 0 -> eq_left (remove elt left) pivot right
      | _ -> eq_right left pivot (remove elt right)
    end
    | Left (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> begin
        match uncons right with
        | Is_empty -> Underflow left
        | Pop (pivot, right) -> left_right left pivot right
      end
      | cmp when cmp < 0 -> left_left (remove elt left) pivot right
      | _ -> left_right left pivot (remove elt right)
    end
    | Right (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> begin
        match uncons right with
        | Pop (pivot, right) -> right_right left pivot right
      end
      | cmp when cmp < 0 -> right_left (remove elt left) pivot right
      | _ -> right_right left pivot (remove elt right)
    end

  let remove elt (T t) =
    match remove elt t with
    | Uk t -> T t
    | Underflow t -> T t
end
