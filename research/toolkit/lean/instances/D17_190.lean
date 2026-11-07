import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 190 of the cap-17 certificate: slots 97280 .. 97791 -/
theorem chk_190 : chunkCheck 17 T stdSt 97280 512 = true := by decide +kernel

end Row17
