module AVL
open FStar.Tactics

type tree =
     | Leaf : tree
     | Node : key:int -> l:tree -> r:tree -> ah:int -> tree

val in_tree : x:int -> t:tree -> Tot bool
let rec in_tree x = function
  | Leaf -> false
  | Node y l r _ -> y = x || in_tree x l || in_tree x r

val all_tree : f:(int-> Tot bool) -> t:tree -> Tot (r:bool {r = true <==> (forall y. in_tree y t ==> f y)})
let rec all_tree f = function
    | Leaf -> true
    | (Node k l r _) -> f k && all_tree f l && all_tree f r

val all_more_than : k:int -> t:tree -> Tot (r:bool {r <==> (forall x. in_tree x t ==> x > k)})
let all_more_than k = all_tree (fun x -> x > k)

val all_less_than : k:int -> t:tree -> Tot (r:bool {r <==> (forall x. in_tree x t ==> x < k)})
let all_less_than k = all_tree (fun x -> x < k)

val is_bst : tree -> Tot bool
let rec is_bst = function
    | Leaf -> true
    | (Node k l r _) -> all_less_than k l && all_more_than k r && is_bst l && is_bst r

val max : x:int -> y:int -> Tot (r:int {r = x \/ r = y})
let max x y = if x > y then x else y

val real_height : t:tree -> Tot int

let rec real_height = function
  | Leaf -> 0
  | Node _ l r _ ->
    let hl = real_height l in
    let hr = real_height r in
    1 + max hl hr

val node_height : tree -> tree -> Tot int
let node_height l r =
  let hl = real_height l in
  let hr = real_height r in
  1 + max hl hr

val is_real_h : int -> tree -> tree -> Tot bool
let is_real_h v l r = v = node_height l r

val has_real_heights : tree -> Tot bool
let rec has_real_heights = function
  | Leaf -> true
  | Node _ l r ah -> is_real_h ah l r && has_real_heights l && has_real_heights r

val get_height : t:tree {has_real_heights t} -> Tot (r:int {r = real_height t})
let get_height = function
    |Leaf -> 0
    | Node _ _ _ h -> h

val has_bal : int -> tree -> tree -> Tot bool
let has_bal x l r =
  let d = real_height l - real_height r in
  0 - x <= d && d <= x

val is_bal : tree -> Tot bool
let rec is_bal = function
  | Leaf -> true
  | Node _ l r _ -> has_bal 1 l r && is_bal l && is_bal r

val is_avl : tree -> Tot bool
let is_avl t = is_bst t && has_real_heights t && is_bal t

type avl = t:tree {is_avl t}

(* trees of height N *)
type avln (n:int) = t:avl {real_height t = n}
(* trees of height equal to that of another T *)
type avlt (t:tree) = avln (real_height t)
type avll (k:int) = t:avl {all_less_than k t}
(* trees of height equal to that of another T *)
type avlr (k:int) = t:avl {all_more_than k t}

val empty : avln 0
let empty = Leaf

val singleton : int -> avln 1
let singleton x =  Node x empty empty 1

val mk_node : v:int -> l:(avll v) -> r:avlr v {has_bal 1 l r} -> Tot (t:avln (node_height l r ) {(forall y. in_tree y t <==> in_tree y l \/ in_tree y r \/ v = y)})
let mk_node v l r =
 let hl = get_height l in
 let hr = get_height r in
 let h = 1 + max hl hr in
   Node v l r h

val is_empty : t:tree -> Tot bool
let is_empty = function
  | Leaf -> true
  | Node _ _ _ _ -> false

val not_empty : t:tree -> Tot bool
let not_empty t = not (is_empty t)

val head: t:tree {not_empty t} -> Tot int
let head (Node x _ _ _) = x

val left: t:tree {not_empty t} -> Tot tree
let left (Node _ l _ _) = l

val right: t:tree {not_empty t} -> Tot tree
let right (Node _ _ r _) = r

val left_of_avl_is_avll : t:avl{not_empty t} -> y:int {y == head t } -> Lemma(all_less_than y (left t))
let left_of_avl_is_avll t y = ()

val real_diff : s:tree -> t:tree -> Tot int
let real_diff s t = real_height s - real_height t

val diff : s:tree {has_real_heights s} -> t:tree {has_real_heights t} -> Tot (r:int {r = real_diff s t} )
let diff s t = get_height s - get_height t

val get_balfac : t:tree {has_real_heights t} -> Tot int
let get_balfac = function
  | Leaf -> 0
  | Node _ l r _ -> diff l r

val is_left_heavy : t:tree{has_real_heights t} -> Tot bool
let is_left_heavy t = get_balfac t > 0

val is_right_heavy : t:tree {has_real_heights t} -> Tot bool
let is_right_heavy t = get_balfac t < 0

val is_not_heavy : t:tree {has_real_heights t} -> Tot bool
let is_not_heavy t = get_balfac t = 0

val is_left_big: l:tree{has_real_heights l} -> r:tree{has_real_heights r} -> Tot bool
let is_left_big l r = diff l r = 2

val is_right_big : l:tree{has_real_heights l} -> r:tree{has_real_heights r} -> Tot bool
let is_right_big l r = diff r l = 2

val all_more_transitive: v:int -> x:int {x > v} -> l:tree {all_more_than x l} -> Lemma (all_more_than v l)
let all_more_transitive v x l = ()

val all_less_transitive: v:int -> x:int {x <= v} -> l:tree {all_less_than x l} -> Lemma (all_less_than v l)
let all_less_transitive v x l = ()

val all_more_intro: v:int -> x:int {x > v} -> l:avll x {all_more_than v l} -> r:avlr x{all_more_than v r && has_bal 1 l r} -> Lemma (all_more_than v (mk_node x l r))
let all_more_intro v x l r  = ()

val all_less_intro: v:int -> x:int {x < v} -> l:avll x {all_less_than v l} -> r:avlr x {all_less_than v r && has_bal 1 l r} -> Lemma ((all_less_than v (mk_node x l r)))
let all_less_intro v x l r  = ()

let impossible = x:int{false}

val balL0 : x:int -> l:avll x {is_not_heavy l} -> r:avlr x {is_left_big l r} -> Tot (t:avln (real_height l + 1) {(forall y. in_tree y t <==> in_tree y l \/ in_tree y r \/ x = y)})
let balL0 x l r = match l with
  | (Node lv ll lr _) ->
    let y = mk_node x lr r in
    all_more_transitive lv x r;
    mk_node lv ll y
  | _ -> admit ()

val balLL : x:int -> l:avll x {is_left_heavy l} -> r:avlr x {is_left_big l r} -> Tot (avlt l)
let balLL v (Node lv ll lr _) r =
  all_more_transitive lv v r;
  mk_node lv ll (mk_node v lr r)

val eq_or_up : s:tree{has_real_heights s} -> t:tree{has_real_heights t} -> Tot bool
let eq_or_up s t =
  let d = diff t s in
  d = 0 || d = 1

val bal_ht : l:tree -> r:tree -> t:tree -> Tot bool
let bal_ht l r t = not (has_bal 1 l r) || is_real_h (real_height t) l r

val big_ht : l:tree{has_real_heights l} -> r:tree{has_real_heights r} -> t:tree{has_real_heights t} -> Tot bool
let big_ht l r t =
  let hl = real_height l in
  let hr = real_height r in
  let l_big    = not (hl >= hr) || (eq_or_up l t) in
  let r_big    = (hl >= hr)     || (eq_or_up r t) in
  l_big && r_big

val re_bal : l:tree {has_real_heights l} -> r:tree {has_real_heights r} -> t:tree{has_real_heights t} -> Tot bool
let re_bal l r t = big_ht l r t && bal_ht l r t

val balLR :x:int  -> l:avll x {is_right_heavy l} -> r:avlr x {is_left_big l r} -> Tot (t:avlt l  {(forall y. in_tree y t <==> in_tree y l \/ in_tree y r \/ x = y)})
let balLR v l r = match l with
  | (Node lv ll (Node lrv lrl lrr lrh) lh) ->
    let y = mk_node v lrr r in

    all_more_transitive lrv v r;
    all_less_transitive lrv lv ll;

    mk_node lrv (mk_node lv ll lrl) (y)
  | _ ->
    (* should be impossible *)
    admit()


val balR0 : x:int  -> r:avlr x {is_not_heavy r} -> l:avll x {is_right_big l r} -> Tot (t:avln (real_height r + 1) {(forall y. in_tree y t <==> in_tree y l \/ in_tree y r \/ x = y)})
let balR0 x r l = match r with
  | (Node rv rl rr _) ->
    all_less_transitive rv x l;
    mk_node rv (mk_node x l rl) rr
  | _ ->
   (* should be impossible *)
    admit ()


val balRR : x:int -> l:avll x -> r:avlr x {is_right_big l r && is_right_heavy r} -> Tot (t:avlt r { (forall y. in_tree y t <==> in_tree y l \/ in_tree y r \/ x = y)})
let balRR x l (Node rv rl rr _) =
  all_less_transitive rv x l;
  mk_node rv (mk_node x l rl) rr

val balRL : x:int -> l: avll x -> r:avlr x {is_right_big l r && is_left_heavy r} -> Tot (t:avlt r {(forall y. in_tree y t <==> in_tree y l \/ in_tree y r \/ x = y)})
let balRL x l = function
  | (Node rv (Node rlv rll rlr _) rr _) ->
    all_less_transitive rlv x l;
    all_more_transitive rlv rv rr;
    mk_node rlv (mk_node x l rll ) (mk_node rv rlr rr)
  | _ ->
    (* should be impossible *)
    admit ()

val no_balancing_needed : l:tree {has_real_heights l } -> r:tree {has_real_heights r /\ has_bal 2 l r /\ not (is_left_big l r) /\ not (is_right_big l r)} -> Lemma (has_bal 1 l r)
let no_balancing_needed l r = ()

val bal : x:int -> l:avll x -> r:avlr x {has_bal 2 l r} -> Tot (t:avl {re_bal l r t /\ (forall y. in_tree y t <==> in_tree y l \/ in_tree y r \/ x = y)})
let bal v l r  =
  let ilb = is_left_big l r in
  let irb = is_right_big l r in
  if (ilb && is_left_heavy l) then balLL v l r
  else if (ilb && is_right_heavy l) then balLR v l r
  else if (ilb) then balL0 v l r
  else if (irb && is_left_heavy r) then balRL v l r
  else if (irb && is_right_heavy r) then balRR v l r
  else if (irb) then balR0 v r l
  else begin
    no_balancing_needed l r;
    mk_node v l r
  end


val in_tree_less_than_lemma : v:int -> t:tree {forall y. (in_tree y t ==> y < v)} -> Lemma (all_less_than v t)
let in_tree_less_than_lemma v t = ()


val in_tree_more_than_lemma : v:int -> t:tree {forall y. (in_tree y t ==> y > v)} -> Lemma (all_more_than v t)
let in_tree_more_than_lemma v t = ()


val less_than_in_tree_lemma : v:int -> t:tree {all_less_than v t} -> Lemma (forall y. (in_tree y t ==> y < v))
let less_than_in_tree_lemma v t = ()


val more_than_in_tree_lemma : v:int -> t:tree {all_more_than v t} -> Lemma (forall y. (in_tree y t ==> y > v))
let more_than_in_tree_lemma v t = ()

val bal_not_empty : x:int -> l:avll x -> r:avlr x {has_bal 2 l r} -> Lemma (not_empty (bal x l r))
let bal_not_empty x l r = ()

val bal_height : x:int -> l:avll x -> r:avlr x {has_bal 2 l r} -> Lemma (real_height (bal x l r) = node_height l r \/ real_height (bal x l r) = node_height l r - 1)
let bal_height x l r = ()

val bal_in_tree : x:int -> l:avll x -> r:avlr x {has_bal 2 l r} -> Lemma (forall y. in_tree y (bal x l r) <==> in_tree y l \/ in_tree y r \/ x = y)
let bal_in_tree x l r = ()

val intro_diff_0_or_1_c :t:tree -> s:tree {real_height t - real_height s >= 0 /\ real_height t - real_height s <= 1} -> Lemma (real_diff t s = 0 \/ real_diff t s = 1)
let intro_diff_0_or_1_c t s = ()

val magic_lemma_bal : t:tree -> s:tree -> Lemma (real_height t - real_height s >= 0 /\ real_height t - real_height s <= 1)
let magic_lemma_bal  t s = admit ()

val insert: x:int -> s:avl -> Tot (t:avl {not_empty t /\ eq_or_up s t /\ (forall y. (in_tree y t) <==> (in_tree y s \/ x = y))})
let rec insert x s = match s with
  | Leaf -> singleton x
  | Node v l r _ ->
    if x < v then begin
      let insl = insert x l in
      less_than_in_tree_lemma v l;
      in_tree_less_than_lemma v insl;
      bal_not_empty v insl r;
      bal_height v insl r;
      bal_in_tree v insl r;
      intro_diff_0_or_1_c (bal v insl r) s;
      assert (forall y. (in_tree y (bal v insl r)) <==> (in_tree y s \/ x = y));
      assert (not_empty (bal v insl r));
      assert (eq_or_up s (bal v insl r));
      bal v insl r
    end else if x > v then begin
      let insr = insert x r in
      more_than_in_tree_lemma v r;
      in_tree_more_than_lemma v insr;
      bal_not_empty v l insr;
      bal_height v l insr;
      bal_in_tree v l insr;
      (assert (forall y. in_tree y insr <==> in_tree y r \/ x = y));
      in_tree_more_than_lemma v insr;
      intro_diff_0_or_1_c (bal v l insr) s;
      assert (eq_or_up s (bal v l insr));
      assert (not_empty (bal v l insr));
      assert (forall y. (in_tree y s) <==> in_tree y l \/ in_tree y r \/ v = y);

      assert (forall y. (in_tree y (bal v l insr)) <==> (in_tree y l \/ in_tree y r \/ v = y \/ x = y));
      assert (forall y. (in_tree y (bal v l insr)) <==> (in_tree y s \/ x = y));
      assert (not_empty (bal v l insr));
      assert (eq_or_up s (bal v l insr));
      bal v l insr
    end else s
