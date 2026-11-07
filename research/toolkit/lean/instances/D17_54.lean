import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 54 of the cap-17 certificate: slots 27648 .. 28159 -/
theorem chk_54 : chunkCheck 17 T stdSt 27648 512 = true := by decide +kernel

end Row17
