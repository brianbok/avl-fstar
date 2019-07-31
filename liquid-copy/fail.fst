module AVL

type ordlist (#a:Type) (ord:  bool)=
     | Nil : ordlist #a
     