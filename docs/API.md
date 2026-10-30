# Integrating PVL into another lab

`src/core.js` exports the same object to Node (`require`) and browser (`PVL`). No code is evaluated from a user string. The supported top-level numerical entry point is `integrate(config, queryPoints)`; it always calls `scan(config)` first and throws with an attached audit if any check is FAIL or UNRESOLVED.

```javascript
const PVL = require('./src/core.js');
const input = PVL.config({preset:'dipole', winding:1, core:0.32, resolution:80});
const audit = PVL.scan(input);
if (audit.eligible) {
  const result = PVL.integrate(input, [[0.37,1.13],[-1.51,0.73]]);
  console.log(result.velocities, result.circulationCaptured);
}
```

| Input | Meaning |
|---|---|
| `preset` | `single`, `dipole`, `pair`, or `quadrupole` |
| `winding` | Integer multiplier of the preset's signed winding list, absolute value ≤4 |
| `core` | Positive blob radius, 0.08–1 in the supported API |
| `phase`, `angle` | Global complex phase and active spatial orientation, in radians |
| `frame` | Constant angular speed, absolute value ≤2 |
| `scale` | Positive dimensionless ℏ/m, ≤10; UI fixes it at 1 |
| `extent` | Half-width of the quadrature square, 3–12; UI fixes it at 4 |
| `resolution` | Integer source count along one axis, 16–160 |
| `fault` | `none` for ordinary operation; named negative controls are for testing |
| `boundary` | Must be `whole-plane-decay` |
| `representation` | Must be `polar-vortex` |

Query points must be finite two-component arrays in these coordinates. The API checks that 1–16384 points are supplied and every coordinate has magnitude at most 1e6; malformed queries are rejected before source allocation. There is no dimensional inference or local U(1) gauge transformation in this schema. The low-level formulas are exposed for tests and inspection and are not independently gated; callers requiring the contract must use `integrate`.

To add a new family, define its field object, transformation action, domain assumptions, analytic/numerical oracle, and negative controls explicitly. Add a registry case and freeze its acceptance thresholds before running it. Do not map an unknown expression to an existing model merely because it contains familiar tokens. A complete symbolic integration would need typed expressions, operator and boundary semantics, theorem-instance matching, and a separate proof of the compiler/evaluator bridge; this version deliberately records that obligation as unresolved.
