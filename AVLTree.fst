module AVLTree

val max : int -> int -> Tot int
let max i1 i2 = if i1 > i2 then i1 else i2
let _ = assert (forall x y. max x y >= x
                && max x y >= y
                && (max x y = x || max x y = y))

type tree =
  | Leaf : tree
  | Node : int -> (tree * nat) -> (tree * nat) -> tree

type heighted_tree = tuple2 tree nat

val height: tree -> Tot nat

let rec height t = 
	match t with
	| Leaf -> 0
	| Node _ (t1,h1) (t2, h2) -> (max h1 h2) + 1
	
val is_empty: tree -> bool
let is_empty t =
	match t with 
	| Leaf -> true
	| _ -> false
	
type empty_tree = t:tree{is_empty t}
type nonempty_tree = t:tree{not (is_empty t)}

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf -> false
  | Node n (t1, h1) (t2, h2) -> x = n || in_tree x t1 || in_tree x t2

val all : p:(int -> Tot bool) -> t:tree ->
            Tot (r:bool{r <==> (forall x. in_tree x t ==> p x)})
let rec all p t =
  match t with
  | Leaf -> true
  | Node n (t1, h1) (t2, h2) -> p n && all p t1 && all p t2

val is_bst : tree -> Tot bool
let rec is_bst t =
  match t with
  | Leaf -> true
  | Node n (t1, _) (t2, _) -> all (fun n' -> n > n') t1 &&
                    all (fun n' -> n < n') t2 && is_bst t1 && is_bst t2

type bst = t:tree{is_bst t}                   

val create_tree: n:int -> tree 
    -> tree -> Tot tree
let create_tree n t1 t2 =
	Node n (t1, height t1) (t2, height t2)
	
	
val bf: tree -> int
let bf t = match t with
    | Leaf -> 0
    | Node _ (_, h1) (_, h2) -> h1 - h2

val is_balanced: t:tree -> Tot bool
let rec is_balanced t =
    match t with
    | Leaf -> true
    | Node n (t1, h1) (t2, h2) -> is_balanced t1 && is_balanced t2 &&
                    abs (bf t) <= 1

val is_avl: t:tree -> Tot bool
let is_avl t = 
    is_bst t && is_balanced t 

type avl = t:tree{is_avl t}
                    
val search : x:int -> t:tree{is_bst t} ->
  Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | Leaf -> false
  | Node n (t1, h1) (t2, h2) -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

val insert_bst : x:int -> t:bst ->
  Tot (r:bst{(forall y. in_tree y r <==> (in_tree y t \/ x = y))})
let rec insert_bst x t =
  match t with
  | Leaf -> create_tree x Leaf Leaf
  | Node n (t1, h1) (t2, h2) -> 
					if x = n then      t
                    else if x < n then create_tree n (insert_bst x t1) t2
                    else               create_tree n t1 (insert_bst x t2)

val rebalance: t:tree -> Tot tree
let rec rebalance t = 
  if is_balanced t then t
  else match t with
      Node _ (tl, hl) (tr, hr) ->
          if bf t = 2 then
            if bf tl <> -1 then t
            else t
          else 
            if bf tr <> -1 then t
            else t
  
val insert_avl: x:int -> t:avl -> 
  Tot (r:tree{ (forall y. in_tree y r <==> (in_tree y t \/ x = y))})

let rec insert_avl x t = 
    rebalance (match t with
  | Leaf -> create_tree x Leaf Leaf
  | Node n (t1, h1) (t2, h2) -> if x = n then      t
                    else if x < n then create_tree n (insert_avl x t1) t2
                    else               create_tree n t1 (insert_avl x t2))


val left_rotate: t:bst  -> Tot (r:bst)
let rec left_rotate t =
    match t with 
    |   Leaf -> Leaf  
    |   Node x (a_tree, _) (y_tree, h2) ->
        match y_tree with
        |   Leaf -> t 
        |   Node y (b_tree, _) (c_tree, _) ->
            create_tree y (create_tree x a_tree b_tree) c_tree


val create_tree_keeps_elems: n:int -> t1:tree{is_bst t1} -> t2:tree{is_bst t2} ->
    Lemma(forall y. in_tree y (create_tree n t1 t2) <==> in_tree y t1  \/ in_tree y t2 \/ n = y) 

let rec create_tree_keeps_elems n t1 t2 = 
    ()

val left_rotate_keeps_elements: t:bst -> Lemma(forall y. in_tree y (left_rotate t) <==> in_tree y t )

let rec left_rotate_keeps_elements t =
    ()

val right: tree -> tree
let right t = 
	match t with
	| Node _ (t1, _) (t2, _) -> t2
	| Leaf -> Leaf

val left: tree -> tree
let left t = 
	match t with
	| Node _ (t1, _) (t2, _) -> t1
	| Leaf -> Leaf
	
val is_case_A: t:bst -> bool 
let is_case_A t = 
	bf t = 2 && bf (right t) = 1 && is_avl (right t) && is_avl (left t)
	
		
val bf_2_is_non_empty: t:tree{bf t == 2} -> Lemma(not(is_empty t))
let bf_2_is_non_empty t =
	()
		
type case_A_tree = t:bst{is_case_A t}

val left_rotate_bla: t:case_A_tree -> t2:avl
let left_rotate_bla t = 
	let t2 = left_rotate t in 
	let h = height(left t) in
	assert(height(left (right t)) = h); 
	assert(is_avl t2);
	t2

val left_rotate_case_A_balances: t:case_A_tree -> Lemma(is_avl (left_rotate t))
let left_rotate_case_A_balances t = 
	let h = height(left t) in
	assert(height(left (right t)) == h)
