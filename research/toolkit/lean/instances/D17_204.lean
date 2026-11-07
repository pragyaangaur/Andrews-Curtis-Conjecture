import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 204 of the cap-17 certificate: slots 104448 .. 104959 -/
theorem chk_204 : chunkCheck 17 T stdSt 104448 512 = true := by decide +kernel

end Row17
