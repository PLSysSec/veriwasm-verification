// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
unsigned long pow2(unsigned exponent) {
	unsigned long a = 1;

	for (unsigned i = 0; i < exponent; ++i) {
		a += a;
	}

	return a;
}

int main(int argc, char* argv[]) {
	return pow2(argv[1][0] - '0');
}
