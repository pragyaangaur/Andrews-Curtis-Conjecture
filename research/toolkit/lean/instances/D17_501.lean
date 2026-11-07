import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 501 of the cap-17 certificate: slots 256512 .. 257023 -/
theorem chk_501 : chunkCheck 17 T stdSt 256512 512 = true := by decide +kernel

end Row17
