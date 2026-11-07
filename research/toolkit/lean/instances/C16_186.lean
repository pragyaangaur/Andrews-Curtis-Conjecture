import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 186 of the cap-16 certificate: slots 190464 .. 191487 -/
theorem chk_186 : chunkCheck 16 T stdSt 190464 1024 = true := by decide +kernel

end Row16
