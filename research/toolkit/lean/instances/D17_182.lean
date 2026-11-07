import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 182 of the cap-17 certificate: slots 93184 .. 93695 -/
theorem chk_182 : chunkCheck 17 T stdSt 93184 512 = true := by decide +kernel

end Row17
