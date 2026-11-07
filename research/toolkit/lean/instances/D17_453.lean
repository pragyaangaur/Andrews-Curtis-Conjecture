import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 453 of the cap-17 certificate: slots 231936 .. 232447 -/
theorem chk_453 : chunkCheck 17 T stdSt 231936 512 = true := by decide +kernel

end Row17
