import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 145 of the cap-16 certificate: slots 148480 .. 149503 -/
theorem chk_145 : chunkCheck 16 T stdSt 148480 1024 = true := by decide +kernel

end Row16
