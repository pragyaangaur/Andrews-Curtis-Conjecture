import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 204 of the cap-16 certificate: slots 208896 .. 209919 -/
theorem chk_204 : chunkCheck 16 T stdSt 208896 1024 = true := by decide +kernel

end Row16
