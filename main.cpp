/**
* Smallest Mixed Integer Problem Solver
* Creator: YSR
*    Date: 2016/10/08
*/

#include<algorithm>
#include<cmath>
#include<chrono>
#include<cstdint>
#include<deque>
#include<fstream>
#include<iostream>
#include<sstream>
#include<string>
#include<tuple>
#include<vector>

//! using宣言
using std::cout;
using std::deque;
using std::endl;
using std::string;
using std::vector;

//! 定数宣言
const double EPS = 1.0e-10;	//! 誤差のしきい値

double depth = 1;

//! enum宣言
enum class Compare {
	Less,
	Equal,
	Greater,
};

//! 十分0に近い場合に0へ丸める
double round_to_zero(const double x) {
	return (abs(x) < EPS ? 0.0 : x);
}

//! 整数に十分近い場合にtrue
bool is_int(const double x) {
	return (abs(x - round(x)) < EPS);
}

//! 実数を文字列に変換する(ダンプ用)
string dtos(const double x) {
	std::stringstream ss;
	ss << (x >= 0.0 ? "+" : "-") << " " << abs(x);
	return  ss.str();
}

//! 結果出力用クラス
struct Result {
	double z;			//! 目的関数の値
	vector<double> x;	//! 変数の値
						//! コンストラクタ
	Result() {}
	Result(const size_t size) {
		z = -DBL_MAX;
		x.resize(size);
	}
	//! 出力
	void put() const noexcept {
		cout << "z: " << z << "\n  ";
		for (size_t vi = 0; vi < x.size(); ++vi) {
			if (round_to_zero(x[vi]) != 0.0)
				cout << "x" << (vi + 1) << ": " << x[vi] << " ";
		}
		cout << endl;
	}
};

//! 単体表クラス
struct SimplexModule {
	/**
	* table[行][列]についての説明
	* 行＝0～(e_cnt-1) →
	* 　列＝0 →右辺の係数
	* 　列＝1～v_cnt →左辺の係数
	* 　列＝(v_cnt+1)～(v_cnt+s_cnt) →スラック変数
	* 　列＝(v_cnt+s_cnt+1)～(v_cnt+s_cnt+a_cnt) →人為変数
	* 行＝e_cnt→
	* 　a_cnt＝0なら、列＝1～v_cnt→目的関数の係数
	* 　a_cnt≠0なら、列＝1～v_cnt+s_cnt→目的関数の係数
	*/
	vector<vector<double>> table;	//! 単体表
	vector<size_t> v_idx;			//! 変数の番号
	deque<bool> a_flg;				//! 人為変数ならtrue
	size_t v_cnt, e_cnt, s_cnt, a_cnt;	//! 変数・制約式・スラック変数・人為変数の数
										//! コンストラクタ
	SimplexModule(
		const size_t v_cnt,	//! 変数の数
		const size_t e_cnt,	//! 制約式の数
		const size_t s_cnt,	//! スラック変数の数
		const size_t a_cnt	//! 人為変数の数
	) {
		//! 単体表を初期化
		const size_t simplex_row = e_cnt + 1;
		const size_t simplex_column = v_cnt + s_cnt + a_cnt + 2;
		table.resize(simplex_row);
		for (auto &&it : table) {
			it.resize(simplex_column, 0.0);
		}
		//! その他の初期化
		v_idx.resize(e_cnt);
		a_flg.resize(e_cnt, false);
		this->v_cnt = v_cnt;
		this->e_cnt = e_cnt;
		this->s_cnt = s_cnt;
		this->a_cnt = a_cnt;
	}
	//! 最適化(a_cntの値で変化？)
	bool solve() noexcept {
		size_t count = 1;
		size_t simplex_column = v_cnt + s_cnt + a_cnt;
		while (true) {
			//! 列の選択(Bland の規則)
			size_t column_idx = 0;
			for (int j = 1; j <= simplex_column && column_idx == 0; ++j) {
				if (table[e_cnt][j] < -EPS)
					column_idx = j;
			}
			//! 行の選択
			if (column_idx == 0) {
				//! 最適化終了
				return true;
			}
			else {
				//! 行の選択(Bland の規則)
				size_t row_index = 0;
				double min = 0.0;
				size_t k = SIZE_MAX;
				for (size_t i = 0; i < e_cnt; ++i) {
					//! 非正とみなされる場合は飛ばす
					if (table[i][column_idx] < EPS) continue;
					double temp = table[i][0] / table[i][column_idx];
					if (row_index == 0
						|| temp < min
						|| temp == min && v_idx[i] < k) {
						min = temp;
						row_index = i + 1;
						k = v_idx[i];
					}
				}
				if (row_index == 0) {
					//! 解なし
					return false;
				}
				else {
					row_index = row_index - 1;	//! 1以上なので必ず1を引ける
												//! 単体表の変形処理
					{
						//! まずは選択行を掃き出す
						double temp = table[row_index][column_idx];
						v_idx[row_index] = column_idx - 1;
						for (size_t j = 0; j <= simplex_column; ++j) {
							table[row_index][j] /= temp;
						}
					}
					{
						//! 次に他の行を掃き出す
						for (size_t i = 0; i <= e_cnt; ++i) {
							if (i == row_index) continue;
							double temp = table[i][column_idx];
							for (size_t j = 0; j <= simplex_column; ++j) {
								table[i][j] -= temp * table[row_index][j];
							}
						}
					}
				}
			}
		}
	}
	//! 2段階法において、実行可能解が存在し得るかをチェックする
	bool is_safe() const noexcept {
		return (table[e_cnt][0] >= -EPS);
	}
	//! 単体表を表示する
	void dump() {
		size_t i = 0;
		for (const auto& it1 : table) {
			if (i < e_cnt) {
				cout << "x" << (v_idx[i] + 1);
			}
			else {
				cout << "z";
			}
			for (size_t j = 0; j < v_cnt + s_cnt + a_cnt + 1; ++j) {
				cout << " " << it1[j];
			}
			cout << "\n";
			++i;
		}
		cout << "\n";
	}
};

//! MIPクラス
class MIP {
	size_t v_cnt;	//! 変数の数
	size_t e_cnt;	//! 制約式の数
	vector<double> obj;				//! 目的関数の係数
	vector<vector<double>> e_left;	//! 制約式係の数(左辺)
	vector<Compare> e_compare;		//! 制約式の比較演算子
	vector<double> e_right;			//! 制約式の係数(右辺)
	deque<bool> integer_flg;		//! 整数変数ならtrue
									//! スラック変数および人為変数の数を数える
	std::tuple<size_t, size_t> count_slack_artificial() const {
		size_t s_cnt = 0, a_cnt = 0;
		for (size_t i = 0; i < e_cnt; ++i) {
			//! 各制約式を見て判断する
			if (e_compare[i] == Compare::Equal) {
				//! 等号なら人為変数＋1
				++a_cnt;
			}
			else {
				//! 不等号ならスラック変数＋1
				++s_cnt;
				//! 基底可能解を求めるために、人為変数が必要な場合に＋1
				if (e_right[i] < 0.0  && e_compare[i] == Compare::Less
					|| e_right[i] >= 0.0 && e_compare[i] == Compare::Greater) {
					++a_cnt;
				}
			}
		}
		return std::make_tuple(s_cnt, a_cnt);
	}
	//! 単体表を作成する
	SimplexModule make_simplex_table(const size_t s_cnt, const size_t a_cnt) const {
		//! 領域を初期化
		SimplexModule sm(v_cnt, e_cnt, s_cnt, a_cnt);
		//! 数値で埋めていく
		//! 制約式の係数で初期化する
		for (size_t i = 0; i < e_cnt; ++i) {
			sm.table[i][0] = e_right[i];
			for (size_t j = 0; j < v_cnt; ++j) {
				sm.table[i][j + 1] = e_left[i][j];
			}
		}
		for (size_t i = 0; i < e_cnt; ++i) {
			if (sm.table[i][0] < 0.0) {
				for (size_t j = 0; j <= v_cnt; ++j) {
					sm.table[i][j] = -sm.table[i][j];
				}
			}
		}
		//! スラック変数を配置する
		size_t idx = v_cnt + 1;
		for (size_t i = 0; i < e_cnt; ++i) {
			if (e_compare[i] != Compare::Equal) {
				if (e_right[i] < 0.0  && e_compare[i] == Compare::Less
					|| e_right[i] >= 0.0 && e_compare[i] == Compare::Greater) {
					sm.table[i][idx] = -1.0;
				}
				else {
					sm.table[i][idx] = 1.0;
					sm.v_idx[i] = idx - 1;
				}
				++idx;
			}
		}
		//! 人為変数を配置する
		for (size_t i = 0; i < e_cnt; ++i) {
			if (e_right[i] < 0.0  && e_compare[i] != Compare::Greater
				|| e_right[i] >= 0.0 && e_compare[i] != Compare::Less) {
				sm.table[i][idx] = 1.0;
				sm.v_idx[i] = idx - 1;
				sm.a_flg[i] = true;
				++idx;
			}
		}
		//! 目的関数を用意する
		if (a_cnt == 0) {
			for (size_t i = 0; i < v_cnt; ++i) {
				sm.table[e_cnt][i + 1] = -obj[i];
			}
		}
		else {
			for (size_t i = 0; i < e_cnt; ++i) {
				if (!sm.a_flg[i]) continue;
				for (size_t j = 0; j <= v_cnt + s_cnt; ++j) {
					sm.table[e_cnt][j] -= sm.table[i][j];
				}
			}
		}
		return sm;
	}
	//! 目的関数を書き換える(2段階法用)
	void change_z_param(const size_t s_cnt, SimplexModule &sm) const noexcept {
		for (size_t j = 0; j <= v_cnt + s_cnt; ++j) {
			sm.table[e_cnt][j] = 0.0;
		}
		for (size_t j = 1; j <= v_cnt; ++j) {
			sm.table[e_cnt][j] = -obj[j - 1];
		}
		for (size_t j = 0; j <= v_cnt + s_cnt; ++j) {
			for (size_t i = 0; i < e_cnt; ++i) {
				if (sm.v_idx[i] < v_cnt) {
					//! 本来の変数の範囲内だと、係数＝目的関数の係数
					sm.table[e_cnt][j] += obj[sm.v_idx[i]] * sm.table[i][j];
				}
				else if (sm.v_idx[i] < v_cnt + s_cnt) {
					//! スラック変数の範囲内だと、係数＝0
				}
				else {
					//! 人為変数の範囲内だと、係数＝-1
					sm.table[e_cnt][j] += (-1.0) * sm.table[i][j];
				}
			}
		}
	}
	//! 分枝操作
	void split_branch(const size_t index, const double border, const Compare mode) {
		//! 制約式の数
		++e_cnt;
		//! 制約式の左辺
		vector<double> temp(v_cnt, 0.0);
		temp[index] = 1.0;
		e_left.push_back(temp);
		//! 制約式の不等号
		e_compare.push_back(mode);
		//! 制約式の右辺
		if (mode == Compare::Less) {
			e_right.push_back(floor(border));
		}
		else {
			e_right.push_back(ceil(border));
		}
	}
public:
	//! コンストラクタ
	MIP(const char file_name[]) {
		std::ifstream ifs(file_name, std::ios::in);
		if (ifs.fail())
			throw "ファイルが読み込めません.";
		//! 変数の数、および制約式の数を読み込む
		ifs >> v_cnt >> e_cnt;
		//! バッファを初期化
		obj.resize(v_cnt, 0.0);
		e_left.resize(e_cnt, vector<double>(v_cnt, 0.0));
		e_compare.resize(e_cnt, Compare::Equal);
		e_right.resize(e_cnt, 0.0);
		integer_flg.resize(v_cnt, false);
		//! 目的関数を読み込む
		for (auto &&it : obj)
			ifs >> it;
		//! 制約式を読み込む
		for (size_t ei = 0; ei < e_cnt; ++ei) {
			//! 左辺の係数
			for (size_t vi = 0; vi < v_cnt; ++vi) {
				ifs >> e_left[ei][vi];
			}
			//! 比較演算子
			{
				std::string temp;
				ifs >> temp;
				if (temp == "<")
					e_compare[ei] = Compare::Less;
				else if (temp == "=")
					e_compare[ei] = Compare::Equal;
				else if (temp == ">")
					e_compare[ei] = Compare::Greater;
				else
					throw std::to_string(ei + 1) + "行目の制約式の比較演算子に誤りがあります.";
			}
			//! 右辺の係数
			ifs >> e_right[ei];
		}
		//! 整数条件を読み込む
		for (size_t vi = 0; vi < v_cnt; ++vi) {
			int temp;
			ifs >> temp;
			integer_flg[vi] = (temp != 0);
		}
	}
	//! 中身を表示
	void put() const noexcept {
		//! 目的関数を出力
		cout << "maximize\n  ";
		for (size_t i = 0; i < v_cnt; ++i) {
			cout << dtos(obj[i]) << " x" << (i + 1) << " ";
		}
		//! 制約式を出力
		cout << "\nsubject to\n";
		for (size_t i = 0; i < e_cnt; ++i) {
			cout << "  ";
			//! 左辺
			for (size_t j = 0; j < v_cnt; ++j) {
				cout << dtos(e_left[i][j]) << " x" << (j + 1) << " ";
			}
			//! 比較演算子
			std::string temp{ "<=>" };
			cout << temp[(size_t)e_compare[i]] << "= ";
			//! 右辺
			cout << e_right[i] << "\n";
		}
		//! 整数条件を出力
		cout << "general\n  ";
		for (size_t i = 0; i < v_cnt; ++i) {
			if (integer_flg[i]) {
				cout << "x" << (i + 1) << " ";
			}
		}
		cout << endl;
	}
	//! 最適化を行う(LP)
	Result pre_optimize() const {
		Result result(v_cnt);	//! デフォルト値は"実行不可能"であることに注意
								//! スラック変数および人為変数の数を数える
		size_t s_cnt, a_cnt;
		std::tie(s_cnt, a_cnt) = count_slack_artificial();
		//! 単体表を作成する
		auto sm = make_simplex_table(s_cnt, a_cnt);
		//! 単体表を変形させる
		if (a_cnt > 0) {	//! 人為変数が存在する場合
			//! 途中で変形不能＝実行不可能
			if (!sm.solve())
				return result;
			//! 「最大値」の項が負だったとしても実行不可能
			if (!sm.is_safe())
				return result;
			//! 目的関数を書き換える
			change_z_param(s_cnt, sm);
			sm.a_cnt = 0;
			//! 再度変形させる
			if (!sm.solve())
				return result;
		}
		else {
			//! 人為変数が存在しない場合
			if (!sm.solve())
				return result;
		}
		//! 結果を出力する
		result.z = sm.table[e_cnt][0];
		for (size_t i = 0; i < e_cnt; ++i) {
			if (sm.v_idx[i] < v_cnt) {
				result.x[sm.v_idx[i]] = sm.table[i][0];
			}
		}
		if (result.z >= DBL_MAX)
			result.z = -DBL_MAX;
		return result;
	}
	//! 最適化を行う(MIP)
	Result optimize() const {
		Result result(v_cnt);
		return optimize(result);
	}
	Result optimize(const Result lower_bound) const {
		//! まずは緩和問題を解く
		auto pre_result = pre_optimize();
		cout << "緩和問題(" << depth << ")の解：\n";
		pre_result.put();
		//! 限定操作
		if (pre_result.z <= lower_bound.z)
			return lower_bound;
		//! 緩和問題の解が整数条件を満たす場合はそのまま出力する
		size_t idx = 0;
		for (size_t i = 0; i < v_cnt; ++i) {
			if (integer_flg[i] && !is_int(pre_result.x[i])) {
				idx = i + 1;
				break;
			}
		}
		depth++;
		if (idx != 0) {
			//! 分枝操作その1
			auto problem1 = *this;
			problem1.split_branch(idx - 1, pre_result.x[idx - 1], Compare::Less);
			auto result1 = problem1.optimize(lower_bound);
			//! 分枝操作その2
			auto problem2 = *this;
			problem2.split_branch(idx - 1, pre_result.x[idx - 1], Compare::Greater);
			auto result2 = problem2.optimize(result1);
			return result2;
		}
		depth--;
		return pre_result;
	}
};

//! main関数
int main(int argc, char *argv[]) {
	try {
		//! 引数処理
		if (argc < 2)
			throw "引数が足りません.";
		//! ファイルを読み込んで初期化する
		MIP mip(argv[1]);
		mip.put();
		//! 解く
		auto result = mip.optimize();
		//! 結果を表示する
		result.put();
	}
	catch (const char str[]) {
		cout << "エラー：" << str << endl;
	}
	system("pause");
}
