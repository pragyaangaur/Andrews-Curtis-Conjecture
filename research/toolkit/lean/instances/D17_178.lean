import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 178 of the cap-17 certificate: slots 91136 .. 91647 -/
theorem chk_178 : chunkCheck 17 T stdSt 91136 512 = true := by decide +kernel

end Row17
