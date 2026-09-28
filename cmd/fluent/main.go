// Команда запуска анализатора из консоли: fluent ./...
package main

import (
	"golang.org/x/tools/go/analysis/singlechecker"

	"fluent/analyzer"
)

func main() {
	singlechecker.Main(analyzer.Analyzer)
}
