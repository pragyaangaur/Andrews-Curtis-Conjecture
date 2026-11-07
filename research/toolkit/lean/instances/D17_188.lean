import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 188 of the cap-17 certificate: slots 96256 .. 96767 -/
theorem chk_188 : chunkCheck 17 T stdSt 96256 512 = true := by decide +kernel

end Row17
