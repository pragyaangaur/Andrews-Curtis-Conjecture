import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 260 of the cap-17 certificate: slots 133120 .. 133631 -/
theorem chk_260 : chunkCheck 17 T stdSt 133120 512 = true := by decide +kernel

end Row17
