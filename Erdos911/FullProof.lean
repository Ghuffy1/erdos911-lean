import Erdos911.LargeRightBlockRamsey

namespace Erdos911

/-- The exact frozen Erdős 911 statement follows from the full
large-right-block argument and the verified reductions. -/
theorem erdos_911_full_proof : ExactStatement :=
  exact_of_large_right_blocks large_right_block_ramsey_statement

end Erdos911
