import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 174 of the cap-16 certificate: slots 178176 .. 179199 -/
theorem chk_174 : chunkCheck 16 T stdSt 178176 1024 = true := by decide +kernel

end Row16
