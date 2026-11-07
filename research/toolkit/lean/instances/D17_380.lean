import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 380 of the cap-17 certificate: slots 194560 .. 195071 -/
theorem chk_380 : chunkCheck 17 T stdSt 194560 512 = true := by decide +kernel

end Row17
