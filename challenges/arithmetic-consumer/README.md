# Conservative cutoff and complete arithmetic image data

This scope verifies `PalomarConsumer897.consumer_core`: the conservative cutoff, kernel equality for all longer prefixes, the rank-zero case, and complete kernel/image bases with unique rational coordinates. The Challenge and target configuration are unchanged.

The Solution now proves this same proposition directly from `conservative_matrix_kernel` and `certified_theta_image_data`; see `Proof/ConsumerArithmeticCore.lean`. Local exact checks preserve the original proposition and its definition, and the complete exported dependency closure passes strict structural and standard-axiom comparison. The static import graph removes 952 local modules relative to the previous wrapper. Official cold-build and kernel verification remain required for this revision.

This component does not by itself select the complete original geometric consumer endpoint. The original complete recovery proofs and all 103 endpoint obligations remain in the repository. See [validation receipt](../../docs/audit/consumer-direct-proof-1795/receipt.json).
