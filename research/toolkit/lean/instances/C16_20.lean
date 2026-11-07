import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 20 of the cap-16 certificate: slots 20480 .. 21503 -/
theorem chk_20 : chunkCheck 16 T stdSt 20480 1024 = true := by decide +kernel

end Row16
