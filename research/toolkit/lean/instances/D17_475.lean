import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 475 of the cap-17 certificate: slots 243200 .. 243711 -/
theorem chk_475 : chunkCheck 17 T stdSt 243200 512 = true := by decide +kernel

end Row17
