import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 93 of the cap-16 certificate: slots 95232 .. 96255 -/
theorem chk_93 : chunkCheck 16 T stdSt 95232 1024 = true := by decide +kernel

end Row16
