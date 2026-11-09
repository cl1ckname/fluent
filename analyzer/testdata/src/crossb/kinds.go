package crossb

import "crossa"

func kinds(a, b crossa.Kinds) {
	crossa.SameKinds(a, a)
	crossa.SameKinds(a, b) // want `cannot prove a<k> == b<k>` `cannot prove a<e> == b<e>` `cannot prove a<a> == b<a>` `cannot prove a<p> == b<p>` `cannot prove a<ch> == b<ch>`
}
