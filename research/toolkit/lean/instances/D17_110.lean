import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 110 of the cap-17 certificate: slots 56320 .. 56831 -/
theorem chk_110 : chunkCheck 17 T stdSt 56320 512 = true := by decide +kernel

end Row17
