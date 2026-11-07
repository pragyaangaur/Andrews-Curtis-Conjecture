import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 98 of the cap-16 certificate: slots 100352 .. 101375 -/
theorem chk_98 : chunkCheck 16 T stdSt 100352 1024 = true := by decide +kernel

end Row16
