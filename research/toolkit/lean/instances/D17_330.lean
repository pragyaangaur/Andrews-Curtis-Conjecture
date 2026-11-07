import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 330 of the cap-17 certificate: slots 168960 .. 169471 -/
theorem chk_330 : chunkCheck 17 T stdSt 168960 512 = true := by decide +kernel

end Row17
