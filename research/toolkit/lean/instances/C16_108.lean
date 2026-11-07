import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 108 of the cap-16 certificate: slots 110592 .. 111615 -/
theorem chk_108 : chunkCheck 16 T stdSt 110592 1024 = true := by decide +kernel

end Row16
