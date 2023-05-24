Syntax.vo Syntax.glob Syntax.v.beautified Syntax.required_vo: Syntax.v 
Syntax.vio: Syntax.v 
Syntax.vos Syntax.vok Syntax.required_vos: Syntax.v 
Abstract.vo Abstract.glob Abstract.v.beautified Abstract.required_vo: Abstract.v Syntax.vo
Abstract.vio: Abstract.v Syntax.vio
Abstract.vos Abstract.vok Abstract.required_vos: Abstract.v Syntax.vos
Concrete.vo Concrete.glob Concrete.v.beautified Concrete.required_vo: Concrete.v Syntax.vo
Concrete.vio: Concrete.v Syntax.vio
Concrete.vos Concrete.vok Concrete.required_vos: Concrete.v Syntax.vos
