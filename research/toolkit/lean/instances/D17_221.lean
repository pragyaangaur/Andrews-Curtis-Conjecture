import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 221 of the cap-17 certificate: slots 113152 .. 113663 -/
theorem chk_221 : chunkCheck 17 T stdSt 113152 512 = true := by decide +kernel

end Row17
