import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 90 of the cap-16 certificate: slots 92160 .. 93183 -/
theorem chk_90 : chunkCheck 16 T stdSt 92160 1024 = true := by decide +kernel

end Row16
