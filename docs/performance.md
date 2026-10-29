# Performance

Performance is a design requirement. The contracts specify prepared
indexes with agreement lemmas, canonical tries for keys and no list scans in inner loops. Worklist
updates schedule readers of changed unknowns; schedulers can use RPO, WTO nesting or SCC order.
Static dependencies enable these strategies and termination arguments. Query evaluation records
reads and side contributions in one traversal.

Binary fuel avoids unary fuel traversal, while the total solver uses well-founded recursion. A
cut-point certificate stores facts at selected points and recomputes the rest; replay lets observers
consume facts without a second stored map. Structured sequences are balanced when built from lists.
The dominator exactness checker runs a reachability search per node; its cost is not claimed
to be linear. The directly verified LT and Semi-NCA producers establish exactness under their
readiness premises.

The landed e-graph rebuild uses prepared incidence indexes. Its report notes that its congruence
pair universe can be quadratic within an operator bucket; source inspection is not a complexity
proof or benchmark. The interval threshold tree can have linear height for sorted or duplicate
inputs, so its lookup is not claimed to be logarithmic. Consult the individual contracts and
reports for the costs and evidence of each component.

The extraction check scans the selected generated artifacts for `Obj.magic` and the Rules solver
closure for proof-only finite-universe enumeration. Clients select extraction realisations outside
theories. The benchmark measures extracted trie, graph, solver and Rules workloads over generated
inputs. A small TOOL-2 experiment measured sizes 8, 16 and 32 with construction and validation
included; it does not establish scaling or a performance guarantee. Report input sizes, commands,
toolchain, machine and timing or memory measurements; label results as experiments. Near-linear
scaling is an objective to investigate, not an established fact.
