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
  | Node n (t1, h1) (t2, h2) -> all (fun n' -> n > n') t1 &&
                    all (fun n' -> n < n') t2 && is_bst t1 && is_bst t2


val create_tree: n:int -> t1:tree{is_bst t1} 
    -> t2:tree{is_bst t2} -> Tot (r:tree{is_bst r})
let create_tree n t1 t2 =
	Node n (t1, height t1) (t2, height t2)
	
	
val bf: tree -> int
let bf t = match t with
    | Leaf -> 0
    | Node _ (_, h1) (_, h2) -> h1 - h2

val is_balanced: t:tree{is_bst t} -> Tot bool
let rec is_balanced t =
    match t with
    | Leaf -> true
    | Node n (t1, h1) (t2, h2) -> is_balanced t1 && is_balanced t2 &&
                    abs (bf t) <= 1
                    
val search : x:int -> t:tree{is_bst t} ->
  Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | Leaf -> false
  | Node n (t1, h1) (t2, h2) -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

val insert_bst : x:int -> t:tree{is_bst t} ->
  Tot (r:tree{is_bst r /\ (forall y. in_tree y r <==> (in_tree y t \/ x = y))})
let rec insert_bst x t =
  match t with
  | Leaf -> create_tree x Leaf Leaf
  | Node n (t1, h1) (t2, h2) -> if x = n then      t
                    else if x < n then create_tree n (insert_bst x t1) t2
                    else               create_tree n t1 (insert_bst x t2)

val rebalance: t1:tree{is_bst t1} -> Tot tree
let rec rebalance t1 = 
  if is_balanced t1 then t1
  else if bf t1 = 2 then t1
  else t1

val insert_avl: x:int -> t:tree{is_balanced t} -> 
  Tot (r:tree{is_balanced r /\ (forall y. in_tree y r <==> (in_tree y t \/ x = y))})

let rec insert_avl x t = 
    rebalance (match t with
  | Leaf -> create_tree x Leaf Leaf
  | Node n (t1, h1) (t2, h2) -> if x = n then      t
                    else if x < n then create_tree n (insert_avl x t1) t2
                    else               create_tree n t1 (insert_avl x t2))


    

