import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 390 of the cap-17 certificate: slots 199680 .. 200191 -/
theorem chk_390 : chunkCheck 17 T stdSt 199680 512 = true := by decide +kernel

end Row17
