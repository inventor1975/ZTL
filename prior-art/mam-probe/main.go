package main

import (
	"fmt"
	"downstream-memory-admissibility/pkg/bitmask"
	"downstream-memory-admissibility/pkg/evaluate"
	"downstream-memory-admissibility/pkg/tenant"
)

func main() {
	var t, d tenant.IDHash // одинаковые: арендатор и область совпадают

	mask := bitmask.EvaluationMask{
		// вызывающий ТРЕБУЕТ, чтобы память была живой:
		RequiredLifecycle: bitmask.RuntimeFlags(bitmask.FlagLifecycleActive),
		AllowedUseClasses: bitmask.RuntimeFlags(bitmask.ClassUseDecisionSupport),
		SensitivityLimit:  bitmask.RuntimeFlags(bitmask.Tier1Preference),
	}

	cases := []struct {
		name  string
		flags bitmask.MemoryFlags
	}{
		{"жизненный цикл НЕ УСТАНОВЛЕН вовсе", bitmask.ClassUseDecisionSupport},
		{"явно активна", bitmask.FlagLifecycleActive | bitmask.ClassUseDecisionSupport},
		{"явно отозвана", bitmask.FlagLifecycleRevoked | bitmask.ClassUseDecisionSupport},
		{"высшая чувствительность при лимите Tier1",
			bitmask.Tier3HighConsequence | bitmask.ClassUseDecisionSupport},
	}
	for _, c := range cases {
		dec, reason := evaluate.EvaluateMemoryHotPath(t, t, d, d, c.flags, mask)
		fmt.Printf("%-42s -> решение %d  причина %s\n", c.name, dec, reason)
	}
}
