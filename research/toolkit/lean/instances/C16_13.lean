import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 13 of the cap-16 certificate: slots 13312 .. 14335 -/
theorem chk_13 : chunkCheck 16 T stdSt 13312 1024 = true := by decide +kernel

end Row16
