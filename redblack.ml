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
  type red = RED [@@warning "-unused-constructor"]
  type black = BLACK [@@warning "-unused-constructor"]

  type ('height, 'color) tree =
    | Leaf : (zero, black) tree
    | Black : ('h, _) tree * elt * ('h, _) tree -> ('h succ, black) tree
    | Red : ('h, black) tree * elt * ('h, black) tree -> ('h, red) tree

  type t = T : (_, _) tree -> t [@@unboxed]

  let empty = T Leaf

  (* Queries *)

  let rec mem : type h c. elt -> (h, c) tree -> bool =
    fun elt -> function
    | Leaf -> false
    | Black (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> true
      | c when c < 0 -> mem elt left
      | _ -> mem elt right
    end
    | Red (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> true
      | c when c < 0 -> mem elt left
      | _ -> mem elt right
    end

  let mem elt (T tree) = mem elt tree

  let rec to_seq : type h c. (h, c) tree -> elt Seq.t = function
    | Leaf -> Seq.empty
    | Red (left, pivot, right) ->
      Seq.append (to_seq left) @@ Seq.cons pivot (to_seq right)
    | Black (left, pivot, right) ->
      Seq.append (to_seq left) @@ Seq.cons pivot (to_seq right)

  let to_seq (T t) = to_seq t

  (* Add *)

  type ('height, 'color) add_result =
    | Ok_black : ('h succ, black) tree -> ('h succ, black) add_result
    | Ok_red : ('h, red) tree -> ('h, 'c) add_result
    | Overflow :
        ('h, black) tree * elt * ('h, black) tree * elt * ('h, black) tree
        -> ('h, red) add_result

  let rec add : type h c. elt -> (h, c) tree -> (h, c) add_result =
    fun elt tree ->
    match tree with
    | Leaf -> Ok_red (Red (Leaf, elt, Leaf))
    | Black (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> Ok_black tree
      | c when c < 0 -> begin
        match add elt left with
        | Ok_black left -> Ok_black (Black (left, pivot, right))
        | Ok_red left -> Ok_black (Black (left, pivot, right))
        | Overflow (a, b, c, d, e) ->
          Ok_red (Red (Black (a, b, c), d, Black (e, pivot, right)))
      end
      | _ -> begin
        match add elt right with
        | Ok_black right -> Ok_black (Black (left, pivot, right))
        | Ok_red right -> Ok_black (Black (left, pivot, right))
        | Overflow (a, b, c, d, e) ->
          Ok_red (Red (Black (left, pivot, a), b, Black (c, d, e)))
      end
    end
    | Red (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> Ok_red tree
      | c when c < 0 -> begin
        match add elt left with
        | Ok_black left -> Ok_red (Red (left, pivot, right))
        | Ok_red (Red (a, b, c)) -> Overflow (a, b, c, pivot, right)
      end
      | _ -> begin
        match add elt right with
        | Ok_black right -> Ok_red (Red (left, pivot, right))
        | Ok_red (Red (a, b, c)) -> Overflow (left, pivot, a, b, c)
      end
    end

  let add elt (T tree) =
    match add elt tree with
    | Ok_black tree -> T tree
    | Ok_red tree -> T tree
    | Overflow (a, b, c, d, e) -> T (Black (Red (a, b, c), d, e))

  (* Remove *)

  type 'h any_color = Any : ('h, _) tree -> 'h any_color

  let join_left
    : type h. (h, black) tree -> elt -> (h succ, black) tree -> h succ any_color
    =
    fun left pivot right ->
    match right with
    | Black (Red (a, b, c), d, Red (e, f, g)) ->
      Any (Red (Black (left, pivot, a), b, Black (Red (c, d, e), f, g)))
    | Black (Red (a, b, c), d, (Leaf as efg)) ->
      Any (Black (Red (left, pivot, a), b, Red (c, d, efg)))
    | Black (Red (a, b, c), d, (Black _ as efg)) ->
      Any (Black (Red (left, pivot, a), b, Red (c, d, efg)))
    | Black ((Leaf as a), b, c) -> Any (Black (Red (left, pivot, a), b, c))
    | Black ((Black _ as a), b, c) -> Any (Black (Red (left, pivot, a), b, c))

  let join_right
    : type h. (h succ, black) tree -> elt -> (h, black) tree -> h succ any_color
    =
    fun left pivot right ->
    match left with
    | Black (Red (a, b, c), d, Red (e, f, g)) ->
      Any (Red (Black (a, b, Red (c, d, e)), f, Black (g, pivot, right)))
    | Black ((Leaf as a), b, Red (c, d, e)) ->
      Any (Black (Red (a, b, c), d, Red (e, pivot, right)))
    | Black ((Black _ as a), b, Red (c, d, e)) ->
      Any (Black (Red (a, b, c), d, Red (e, pivot, right)))
    | Black (a, b, (Leaf as c)) -> Any (Black (a, b, Red (c, pivot, right)))
    | Black (a, b, (Black _ as c)) -> Any (Black (a, b, Red (c, pivot, right)))

  type ('height, 'color) remove_result =
    | Uk_black : ('height, black) tree -> ('height, _) remove_result
    | Uk_red : ('height, red) tree -> ('height, red) remove_result
    | Underflow : ('h, black) tree -> ('h succ, black) remove_result

  let red_any : type h c. (h, c) tree -> (h, red) remove_result =
    fun t ->
    match t with
    | Leaf -> Uk_black t
    | Black _ -> Uk_black t
    | Red _ -> Uk_red t

  let black_any : type h c. (h, c) tree -> (h succ, black) remove_result =
    fun t ->
    match t with
    | Red (a, b, c) -> Uk_black (Black (a, b, c))
    | Leaf -> Underflow t
    | Black _ -> Underflow t

  let black_left
    : type h c1 c2.
      (h, c1) remove_result -> elt -> (h, c2) tree -> (h succ, black) remove_result
    =
    fun left pivot right ->
    match left with
    | Uk_black left -> Uk_black (Black (left, pivot, right))
    | Uk_red left -> Uk_black (Black (left, pivot, right))
    | Underflow left -> begin
      match right with
      | Red (a, b, c) ->
        let (Any t) = join_left left pivot a in
        Uk_black (Black (t, b, c))
      | Black _ ->
        let (Any result) = join_left left pivot right in
        black_any result
    end

  type ('height, 'color) uncons_result =
    | Is_empty : (zero, black) uncons_result
    | Pop : elt * ('height, 'color) remove_result -> ('height, 'color) uncons_result

  let rec uncons : type h c. (h, c) tree -> (h, c) uncons_result = function
    | Leaf -> Is_empty
    | Red (left, pivot, right) -> begin
      match uncons left with
      | Is_empty -> Pop (pivot, Uk_black right)
      | Pop (elt, Uk_black left) -> Pop (elt, Uk_red (Red (left, pivot, right)))
      | Pop (elt, Underflow left) ->
        let (Any result) = join_left left pivot right in
        Pop (elt, red_any result)
    end
    | Black (left, pivot, right) -> begin
      match uncons left with
      | Pop (elt, left) -> Pop (elt, black_left left pivot right)
      | Is_empty -> Pop (pivot, black_any right)
    end

  let black_right
    : type h c1 c2.
      (h, c1) tree -> elt -> (h, c2) remove_result -> (h succ, black) remove_result
    =
    fun left pivot right ->
    match right with
    | Uk_black right -> Uk_black (Black (left, pivot, right))
    | Uk_red right -> Uk_black (Black (left, pivot, right))
    | Underflow right -> begin
      match left with
      | Black _ ->
        let (Any result) = join_right left pivot right in
        black_any result
      | Red (ll, lp, lr) ->
        let (Any t) = join_right lr pivot right in
        Uk_black (Black (ll, lp, t))
    end

  let red_left
    : type h. (h, black) remove_result -> elt -> (h, black) tree -> (h, red) remove_result
    =
    fun left pivot right ->
    match left with
    | Uk_black left -> Uk_red (Red (left, pivot, right))
    | Underflow left ->
      let (Any result) = join_left left pivot right in
      red_any result

  let red_right
    : type h. (h, black) tree -> elt -> (h, black) remove_result -> (h, red) remove_result
    =
    fun left pivot right ->
    match right with
    | Uk_black right -> Uk_red (Red (left, pivot, right))
    | Underflow right ->
      let (Any result) = join_right left pivot right in
      red_any result

  let rec remove : type h c. elt -> (h, c) tree -> (h, c) remove_result =
    fun elt tree ->
    match tree with
    | Leaf -> Uk_black Leaf
    | Red (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> begin
        match uncons right with
        | Pop (new_pivot, right) -> red_right left new_pivot right
        | Is_empty -> Uk_black Leaf
      end
      | cmp when cmp < 0 -> red_left (remove elt left) pivot right
      | _ -> red_right left pivot (remove elt right)
    end
    | Black (left, pivot, right) -> begin
      match Elt.compare elt pivot with
      | 0 -> begin
        match uncons right with
        | Pop (new_pivot, right) -> black_right left new_pivot right
        | Is_empty -> black_any left
      end
      | cmp when cmp < 0 -> black_left (remove elt left) pivot right
      | _ -> black_right left pivot (remove elt right)
    end

  let remove elt (T t) =
    match remove elt t with
    | Uk_red t -> T t
    | Uk_black t -> T t
    | Underflow t -> T t
end
