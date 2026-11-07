import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 50 of the cap-16 certificate: slots 51200 .. 52223 -/
theorem chk_50 : chunkCheck 16 T stdSt 51200 1024 = true := by decide +kernel

end Row16
