package crossa

// Контракт, который тело не выполняет: импортёр получает предупреждение
// в каждой точке вызова.
// @ returns Amount<c>;
func Wrong(c string) Amount { return Amount{Currency: "fixed"} } // want `cannot prove result 1 satisfies returns`
