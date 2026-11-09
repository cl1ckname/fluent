package crossmid // want package:"structs \\[\\] contracts \\[\\] summaries 2"

// Пакет без спецификаций, который видит bounded-типы: его сводки нужны
// импортёрам.

import "crossa"

func Forward(a *crossa.Account) { crossa.Keep(a) }

func Peek(a *crossa.Account) crossa.Status { return crossa.Touch(a) }
