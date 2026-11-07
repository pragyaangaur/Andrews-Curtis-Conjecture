import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 18 of the cap-16 certificate: slots 18432 .. 19455 -/
theorem chk_18 : chunkCheck 16 T stdSt 18432 1024 = true := by decide +kernel

end Row16
