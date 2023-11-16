import subprocess

from constrain_condition import *


class FunctionModel:
    def __init__(self, steps, bounds):
        self.__bounds_rounds = bounds
        self.__step = steps
        self.__declare = []  # 存储变量
        self.__constraints = []  # 存储约束语句
        self.__assign = []  # 存储赋值约束
        self.__RotateCons_left = ["-", "-", "-", "-", "-", 11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6,
                                  8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8,
                                  13, 6, 5, 12, 7, 5]
        self.__OrderMessageWords_left = ["-", "-", "-", "-", "-", 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
                                         7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8,
                                         1, 2, 7, 0, 6, 13, 11, 5, 12]

        self.__isc = ["-", "-", "-", "-", "-", 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
        self.__isf = ["-", "-", "-", "-", "-", 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
        self.__isv = ["-", "-", "-", "-", "-", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        self.__isk = ["-", "-", "-", "-", "-", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1]
        self.__filterBool_left = ["XOR", "IFX", "ONZ"]

    def save_variable(self, s):

        temp = s + ": BITVECTOR(1);\n"
        if temp not in self.__declare:
            self.__declare.append(temp)
        return s

    def create_constraints(self, X, propagation_trail):
        fun = []
        for maxterm in propagation_trail:
            temp = []
            for i in range(len(maxterm)):
                if maxterm[i] == '1':
                    temp.append('(' + '~' + X[i] + ')')
                elif maxterm[i] == '0':
                    temp.append(X[i])
            fun.append('(' + "|".join(temp) + ')')
        sbox_main = 'ASSERT ' + '&'.join(fun) + '=0bin1' + ';\n'
        return sbox_main

    def right_shift(self, order, num):
        return order[num:] + order[:num]

    def addexp_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v, out_var_d, step):
        """
       本函数表示的是搜索策略2中的一个扩展的模加运算，在算法6中的ADDEXP_MODEL;
       :param step: 步数
       :param in_var_v_0:表示delta-X的v
       :param in_var_d_0:表示delta-X的d
       :param in_var_v_1:表示delta-Y的v
       :param in_var_d_1:表示delta-Y的d
       :param out_var_v:表示delta-Z的v
       :param out_var_d:表示delta-Z的d
       :return:
       声明一个delta-C，其大小为33;
       var_c_v 声明一个delta-C的v,用"cv6" + "_" + step + "_" + str(i)表示;
       var_c_d 声明一个delta-C的d,用"cd6" + "_" + step + "_" + str(i)表示;
       """
        eqn = "% ADDEXP_MODEL\n"
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable("cv6" + "_" + str(step) + "_" + str(0)),
                                                             self.save_variable("cd6" + "_" + str(step) + "_" + str(0)))
        for i in range(32):
            temp = [self.save_variable(in_var_v_0[i]), self.save_variable(in_var_d_0[i]),
                    self.save_variable(in_var_v_1[i]), self.save_variable(in_var_d_1[i]),
                    self.save_variable("cv6" + "_" + str(step) + "_" + str(i)),
                    self.save_variable("cd6" + "_" + str(step) + "_" + str(i)),
                    self.save_variable(out_var_v[i]), self.save_variable(out_var_d[i]),
                    self.save_variable("cv6" + "_" + str(step) + "_" + str(i + 1)),
                    self.save_variable("cd6" + "_" + str(step) + "_" + str(i + 1))]
            eqn += self.create_constraints(temp, addexp_model_constrain)
        self.__constraints.append(eqn)

    def boolfast_model(self, fna, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v,
                       out_var_d):

        print("60:boolfast_model")
        """
        本模型是布尔函数的快速模型，这个模型中不包括其中隐含条件
        :param fna: 表示步数需要去选择合适的布尔函数
        :param in_var_v_0: 表示布尔函数的输入delta-x的v
        :param in_var_d_0: 表示布尔函数的输入delta-x的d
        :param in_var_v_1: 表示布尔函数的输入delta-y的v
        :param in_var_d_1: 表示布尔函数的输入delta-y的d
        :param in_var_v_2: 表示布尔函数的输入delta-z的v
        :param in_var_d_2: 表示布尔函数的输入delta-z的d
        :param out_var_v: 表示布尔函数的输出delta-w的v
        :param out_var_d: 表示布尔函数的输出delta-w的d
        :return:
        """

        if fna == "ONX":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, onx_fast_contsrain)
            self.__constraints.append(eqn)
        elif fna == "XOR":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, xor_fast_contsrain)
            self.__constraints.append(eqn)

        elif fna == "IFZ":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, ifz_fast_contsrain)
            self.__constraints.append(eqn)
        elif fna == "IFX":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, ifz_fast_contsrain)
            self.__constraints.append(eqn)

        elif fna == "ONZ":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, onx_fast_contsrain)
            self.__constraints.append(eqn)

    def boolfull_model(self, fna, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v,
                       out_var_d, in_var_0, in_var_1, in_var_2):
        print("175:boolfull_model")
        if fna == "ONX":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i])]
                eqn += self.create_constraints(temp, onx_full_constrain)
            self.__constraints.append(eqn)
        elif fna == "XOR":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i])]
                eqn += self.create_constraints(temp, xor_full_constrain)
            self.__constraints.append(eqn)

        elif fna == "IFZ":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i])]
                eqn += self.create_constraints(temp, ifz_full_constrain)
            self.__constraints.append(eqn)
        elif fna == "IFX":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i]),
                        self.save_variable(in_var_0[i])]
                eqn += self.create_constraints(temp, ifz_full_constrain)
            self.__constraints.append(eqn)

        elif fna == "ONZ":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_2[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i])]
                eqn += self.create_constraints(temp, onx_full_constrain)
            self.__constraints.append(eqn)

    def computer_q(self, in_var_v_z, in_var_d_z, in_var_v_x, in_var_d_x, in_var_z, in_var_x, in_var_q, step):
        print("236:computer_q")
        """
        根据
        q = delta-a5 ⊟ a1,
        (δq ⊞ q)[0] = (δb3 ⊞ q≫s)[32 − s],
        (δq ⊞ q)[s] = (δb3 ⊞ q≫s)[0].
        计算其中的q，在算法7中
        :param in_var_v_z:表示输入的delta-a5的v
        :param in_var_d_z:表示输入的delta-a5的d
        :param in_var_v_x:表示输入的delta-a1的v
        :param in_var_d_x:表示输入的delta-a1的d
        :param in_var_z:表示delta-a5的获取的直接条件
        :param in_var_x:表示delta-a1的获取的直接条件
        :param in_var_q:计算出来的q
        :param step:步数
        :return:
        """
        for i in range(32):
            self.derive_cond(in_var_x[i], in_var_v_x[i], in_var_d_x[i])
            self.derive_cond(in_var_z[i], in_var_v_z[i], in_var_d_z[i])
        self.val_add_model(in_var_x, in_var_q, in_var_z, 32, step)

    def derive_cond(self, in_var_x, in_var_v_x, in_var_d_x):
        """
         根据x = 0 if (∇x = n); x = 1 if (∇x = u); x is free if (∇x = =)
        :param in_var_x:表示delta-x的隐含条件
        :param in_var_v_x:表示delta-x的v
        :param in_var_d_x:表示delta-x的d
        :return:
        """
        temp = [in_var_x, in_var_v_x, in_var_d_x]
        eqn = self.create_constraints(temp, derive_cond_constrain)
        self.__constraints.append(eqn)

    def expand_model(self, in_var_v, in_var_d, out_var_v, out_var_d, isK, step):
        print("202:expand_model")
        """
        本模型输出扩展模型，有时候存在输出的结果可能会出现损失；
        :param in_var_v: 表示输入z的v
        :param in_var_d:表示输入z的d
        :param out_var_v:表示输出sigma的v
        :param out_var_d:表示输出sigma的d
        :param isK: 用于判断模型使用区别；当isK=1是，固定sigma(out_var_v,out_var_d)复制给z(in_var_v, in_var_d);当isK=0时，
        固定z(in_var_v, in_var_d)复制给sigma(out_var_v,out_var_d)
        :param step:表示步数
        :return:
        本模型需要创建一个中间变量delta-c，"cv7" + "_" + str(step) + "_" + str(i)表示的delta-c的v，"cv7" + "_" + str(step) + "_" + str(i)表示的delta-c的d;
        """
        eqn = "% expand_model\n"
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable("cv7" + "_" + str(step) + "_" + str(0)),
                                                             self.save_variable("cd7" + "_" + str(step) + "_" + str(0)))
        if isK == 1:
            for i in range(32):
                temp = [self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_v[i]),
                        self.save_variable(in_var_d[i]),
                        "cv7" + "_" + str(step) + "_" + str(i),
                        "cd7" + "_" + str(step) + "_" + str(i),
                        self.save_variable("cv7" + "_" + str(step) + "_" + str(i + 1)),
                        self.save_variable("cd7" + "_" + str(step) + "_" + str(i + 1))]
                eqn += self.create_constraints(temp, expand_model_contsrain_2)
            self.__constraints.append(eqn)
        else:
            for i in range(32):
                temp = [self.save_variable(in_var_v[i]),
                        self.save_variable(in_var_d[i]),
                        self.save_variable("cv7" + "_" + str(step) + "_" + str(i)),
                        self.save_variable("cd7" + "_" + str(step) + "_" + str(i)),

                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable("cv7" + "_" + str(step) + "_" + str(i + 1)),
                        self.save_variable("cd7" + "_" + str(step) + "_" + str(i + 1))]
                eqn += self.create_constraints(temp, expand_model_contsrain_1)
            self.__constraints.append(eqn)

    def modadd_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_c_v, in_var_c_d, out_var_v,
                     out_var_d):
        print("245:modadd_model")
        """
        表示模加操作的模型
        :param in_var_v_0: 表示模加操作中的输入delta-x的v
        :param in_var_d_0: 表示模加操作中的输入delta-x的d
        :param in_var_v_1: 表示模加操作中的输入delta-y的v
        :param in_var_d_1: 表示模加操作中的输入delta-y的d
        :param in_var_c_v: 表示模加操作中的进位delta-c的v
        :param in_var_c_d: 表示模加操作中的进位delta-c的d
        :param out_var_v: 表示模加操作中的输出delta-z的v
        :param out_var_d: 表示模加操作中的输出delta-z的d
        :return:
        """
        eqn = ""
        for i in range(32):
            temp = [self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable(in_var_v_1[i]),
                    self.save_variable(in_var_d_1[i]),
                    self.save_variable(in_var_c_v[i]),
                    self.save_variable(in_var_c_d[i]),
                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),
                    self.save_variable(in_var_c_v[i + 1]),
                    self.save_variable(in_var_c_d[i + 1])]
            eqn += self.create_constraints(temp, modadd_model_constrain)
        self.__constraints.append(eqn)

    def rotate_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v_0, out_var_d_0, out_var_v_1,
                     out_var_d_1, c_var_v_0, c_var_d_0):
        print("276:rotate_model")
        """
        计算循环移位差分，位于算法5的第一个搜索策略中;
        :param in_var_v_0: 输入
        :param in_var_d_0: 输入
        :param in_var_v_1: 输入
        :param in_var_d_1: 输入
        :param out_var_v_0: 输出
        :param out_var_d_0: 输出
        :param out_var_v_1: 输出
        :param out_var_d_1: 输出
        :param c_var_v_0: 中间变量
        :param c_var_d_0: 中间变量
        :return:
        """
        temp = [self.save_variable(in_var_v_0),
                self.save_variable(in_var_d_0),
                self.save_variable(in_var_v_1),
                self.save_variable(in_var_d_1),
                self.save_variable(out_var_v_0),
                self.save_variable(out_var_d_0),
                self.save_variable(out_var_v_1),
                self.save_variable(out_var_d_1),
                self.save_variable(c_var_v_0),
                self.save_variable(c_var_d_0)]
        eqn = self.create_constraints(temp, rotate_model_constrain)
        self.__constraints.append(eqn)

    def signed_q_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v,
                       out_var_d, s):
        print("389:signed_q_model")
        """
        使用第一种搜索策略计算sigma-q：∇q[0 : s] = (∇b4 ⊞ ∇c0[0])[0 : s]
        :param in_var_v_0:表示∇b4的输入v
        :param in_var_d_0:表示∇b4的输入d
        :param in_var_v_1:表示∇c0[0]的v
        :param in_var_d_1:表示∇c0[0]的d
        :param in_var_v_2:表示中间变量∇c1的v
        :param in_var_d_2:表示中间变量∇c1的d
        :param out_var_v:表示输出∇q的v
        :param out_var_d:表示输出∇q的d
        :param s:表示位置s
        :return:
        """
        eqn = "%389:signed_q_model\n"
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (in_var_v_2[0], in_var_d_2[0])

        temp = [self.save_variable(in_var_v_0[0]),
                self.save_variable(in_var_d_0[0]),

                self.save_variable(in_var_v_1[0]),
                self.save_variable(in_var_d_1[0]),

                self.save_variable(in_var_v_2[0]),
                self.save_variable(in_var_d_2[0]),

                self.save_variable(out_var_v[0]),
                self.save_variable(out_var_d[0]),

                self.save_variable(in_var_v_2[1]),
                self.save_variable(in_var_d_2[1])]
        eqn += self.create_constraints(temp, modadd_model_constrain)
        for i in range(1, s + 1):
            temp = [self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable("temp_v" + "_" + str(i)),
                    self.save_variable("temp_d" + "_" + str(i)),

                    self.save_variable(in_var_v_2[i]),
                    self.save_variable(in_var_d_2[i]),

                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),

                    self.save_variable(in_var_v_2[i + 1]),
                    self.save_variable(in_var_d_2[i + 1])]
            eqn += self.create_constraints(temp, modadd_model_constrain)
            eqn += "ASSERT temp_v" + "_" + str(i) + " = 0bin0;\n"
            eqn += "ASSERT temp_d" + "_" + str(i) + " = 0bin0;\n"
        self.__constraints.append(eqn)

    def rotate_diff_first(self, s, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v_0, out_var_d_0, in_var_v_2,
                          in_var_d_2, isV, isK, step):
        print("358:rotate_diff_first")
        """
        旋转部分的搜索策略1，计算a5 = a1 ⊞ (delta-b3≪s)===>b4 = b3≪s, b5 = a1 ⊞ b4, a5 = b5.
        :param s:表示循环移位的值
        :param in_var_v_0:表示输入方delta-b3的v
        :param in_var_d_0:表示输入方delta-b3的d
        :param in_var_v_1:表示输入方delta-a1的v
        :param in_var_d_1:表示输入方delta-a1的d
        :param out_var_v_0:表示输出方delta-a5的v
        :param out_var_d_0:表示输出方delta-a5的v
        :param in_var_v_2:中间变量delta-q的v
        :param in_var_d_2:中间变量delta-q的d
        :param isV:用来计算sigma-q的判断，当isV=1时，计算sigma-q，否则不计算;
        :param isK:用来判断是否调用了expand_model,当isK=1，表示需要调用expan_model，否则不用调用;
        :param step:表示步数
        :return:
        需要声明中间变量delta-b4,delta-b5以及delta-c0大小为33,以及声明ch的中间变量
        """
        # 变量b4
        in_var_v_b4 = []
        in_var_d_b4 = []

        for i in range(32):
            in_var_v_b4.append("bv4" + "_" + str(step) + "_" + str(i))
            in_var_d_b4.append("bd4" + "_" + str(step) + "_" + str(i))

        # 变量b5
        in_var_v_b5 = []
        in_var_d_b5 = []
        for i in range(32):
            in_var_v_b5.append("bv5" + "_" + str(step) + "_" + str(i))
            in_var_d_b5.append("bd5" + "_" + str(step) + "_" + str(i))

        # 变量deta c0
        in_var_v_c0 = []
        in_var_d_c0 = []
        for i in range(33):
            in_var_v_c0.append("cv0" + "_" + str(step) + "_" + str(i))
            in_var_d_c0.append("cd0" + "_" + str(step) + "_" + str(i))
        # 构造变量ch
        "chv" + "_" + str(step)
        "chd" + "_" + str(step)
        # ∇b4[i + s mod 32] = ∇b3[i]
        for i in range(30 - s):
            eqn = "ASSERT %s = %s;\nASSERT %s = %s;\n" % (self.save_variable(in_var_v_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_v_0[i]),
                                                          self.save_variable(in_var_d_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_d_0[i]))
            self.__constraints.append(eqn)
        for i in range(32 - s, 30):
            eqn = "ASSERT %s = %s;\nASSERT %s = %s;\n" % (self.save_variable(in_var_v_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_v_0[i]),
                                                          self.save_variable(in_var_d_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_d_0[i]))
            self.__constraints.append(eqn)

        self.rotate_model(in_var_v_0[31 - s], in_var_d_0[31 - s],
                          in_var_v_0[30 - s], in_var_d_0[30 - s],
                          in_var_v_b4[31], in_var_d_b4[31],
                          in_var_v_b4[30], in_var_d_b4[30],
                          in_var_v_c0[0], in_var_d_c0[0])

        self.rotate_model(in_var_v_0[31], in_var_d_0[31],
                          in_var_v_0[30], in_var_d_0[30],
                          in_var_v_b4[(31 + s) % 32], in_var_d_b4[(31 + s) % 32],
                          in_var_v_b4[(30 + s) % 32], in_var_d_b4[(30 + s) % 32],
                          "chv" + "_" + str(step),
                          "chd" + "_" + str(step))
        self.modadd_model(in_var_v_1, in_var_d_1, in_var_v_b4, in_var_d_b4, in_var_v_c0, in_var_d_c0,
                          in_var_v_b5, in_var_d_b5)
        self.expand_model(in_var_v_b5, in_var_d_b5, out_var_v_0, out_var_d_0, isK, step)
        if isV == 1:
            # 变量deta c0
            in_var_v_c1 = []
            in_var_d_c1 = []
            for i in range(33):
                in_var_v_c1.append("cv1" + "_" + str(step) + "_" + str(i))
                in_var_d_c1.append("cd1" + "_" + str(step) + "_" + str(i))
            self.signed_q_model(in_var_v_b4, in_var_d_b4, in_var_v_c0, in_var_d_c0, in_var_v_c1,
                                in_var_d_c1, in_var_v_2, in_var_d_2, s)

    def left_shift(self, order, num):
        """
        表示循环移位
        :param order:
        :param num:
        :return:
        """
        return order[-num:] + order[:-num]

    def rotate_diff_second(self, s, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v_0, out_var_d_0,
                           in_var_v_2, in_var_d_2, isV, isK, step):
        print("450:rotate_diff_second")
        """
        本模型是a5 = delta-a1 ⊞ (delta-b3≪s)的第二种计算策略；
        :param s:
        :param in_var_v_0:表示delta-b3输入的v
        :param in_var_d_0:表示delta-b3输入的d
        :param in_var_v_1:表示delta-a1输入的v
        :param in_var_d_1:表示delta-a1输入的d
        :param out_var_v_0:表示delta-a5输入的v
        :param out_var_d_0:表示delta-a5输入的d
        :param in_var_v_2:sigma-q的v
        :param in_var_d_2:sigma-q的d
        :param isV:表示的赋值
        :param isK:表示在扩展模型中使用的那种方式
        :param step:表示的步数
        :return:
        """
        # 变量b4
        in_var_v_b4 = []
        in_var_d_b4 = []
        for i in range(32):
            in_var_v_b4.append("bv4" + "_" + str(step) + "_" + str(i))
            in_var_d_b4.append("bd4" + "_" + str(step) + "_" + str(i))
        self.expand_model(in_var_v_b4, in_var_d_b4, in_var_v_0, in_var_d_0, isK, step)
        self.addexp_model(in_var_v_1, in_var_d_1, self.left_shift(in_var_v_b4, s), self.left_shift(in_var_d_b4, s),
                          out_var_v_0, out_var_d_0, step)
        eqn = "% 第二种搜索策略\n"
        if isV == 1:
            for i in range(s + 1):
                eqn += "ASSERT %s = %s;\n" % (
                    self.save_variable(in_var_v_2[i]), self.save_variable(in_var_v_b4[(i - s) + 32]))
                eqn += "ASSERT %s = %s;\n" % (
                    self.save_variable(in_var_d_2[i]), self.save_variable(in_var_d_b4[(i - s) + 32]))
            self.__constraints.append(eqn)

    def val_add_model(self, a, b, v, l, step):
        print("570:val_add_model")
        """
        计算模加操作的函数v = (a ⊞ b)[0 : l − 1]
        :param a:表示模加操作的输入
        :param b:表示模加操作的输入
        :param v:表示模加操作的输出
        :param l:表示长度
        :param step:步数
        :return:
        """
        eqn = "ASSERT c" + "_" + str(step) + "_" + str(0) + " = 0bin0;\n"
        for i in range(l):
            temp = [self.save_variable(a[i]),
                    self.save_variable(b[i]),
                    self.save_variable("c" + "_" + str(step) + "_" + str(i)),
                    self.save_variable(v[i]),
                    self.save_variable("c" + "_" + str(step) + "_" + str(i + 1))]
            eqn += self.create_constraints(temp, modadd_model_origin)
        self.__constraints.append(eqn)

    def val_diff_add_model(self, in_var_v_a, in_var_d_a, b, v, l, num, step):
        print("502:val_diff_add_model")
        """
        计算v = (δa ⊞ b)[0 : l − 1]
        :param in_var_v_a: δa的输入的v
        :param in_var_d_a: δa的输入的d
        :param b: 表示b
        :param v: 输出结果
        :param l: 表示长度
        :param num: 表示使用了两次
        :param step: 步数
        :return:
        """
        # 声明一个符号差分

        eqn = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
            self.save_variable("cv" + str(num) + "_" + str(step) + "_" + str(0)),
            self.save_variable("cd" + str(num) + "_" + str(step) + "_" + str(0)))
        for i in range(l):
            temp = [self.save_variable(in_var_v_a[i]),
                    self.save_variable(in_var_d_a[i]),

                    self.save_variable(b[i]),
                    self.save_variable("cv" + str(num) + "_" + str(step) + "_" + str(i)),
                    self.save_variable("cd" + str(num) + "_" + str(step) + "_" + str(i)),

                    self.save_variable("cv" + str(num) + "_" + str(step) + "_" + str(i + 1)),
                    self.save_variable("cd" + str(num) + "_" + str(step) + "_" + str(i + 1)),

                    self.save_variable(v[i])]
            eqn += self.create_constraints(temp, val_diff_add_constrain)

        print("530行代码，val_diff_add_model函数查看其中声明的符号变量:\nASSERT %s" % eqn)
        self.__constraints.append(eqn)

    def rotate_diff_filter(self, s, in_var_v_a5, in_var_d_a5, in_var_v_a1, in_var_d_a1, in_var_v_b3, in_var_d_b3,
                           in_var_v_q, in_var_d_q, in_var_a5, in_var_a1, step):
        print("546:rotate_diff_filter")
        """
        进一步检测矛盾点;a5 = a1 ⊞ (b3≪s)
        :param s:
        :param in_var_v_a5:表示a5的输出v
        :param in_var_d_a5:表示a5的输出d
        :param in_var_v_a1:表示a1的输入v
        :param in_var_d_a1:表示a1的输入d
        :param in_var_v_b3:表示b3的输入v
        :param in_var_d_b3:表示b3的输入d
        :param in_var_v_q:中间变量q的v
        :param in_var_d_q:中间变量q的d
        :param in_var_a5:a5的辅助变量
        :param in_var_a1:a1的辅助变量
        :param step:
        :return:
        """

        # Claim a binary vector q of size 32
        q = []
        for i in range(32):
            q.append("q" + "_" + str(step) + "_" + str(i))
        self.computer_q(in_var_v_a5, in_var_d_a5, in_var_v_a1, in_var_d_a1, in_var_a5, in_var_a1, q, step)
        # Claim a binary vector v0 of size s + 1
        v0 = []
        for i in range(s + 1):
            v0.append("v0" + "_" + str(step) + "_" + str(i))
        self.val_diff_add_model(in_var_v_q, in_var_d_q, q, v0, s + 1, 4, step)
        # Claim a binary vector v1 of size 33 − s
        v1 = []
        for i in range(33 - s):
            v1.append("v1" + "_" + str(step) + "_" + str(i))
        self.val_diff_add_model(in_var_v_b3, in_var_d_b3, self.right_shift(q, s), v1, 33 - s, 5, step)
        eqn = "ASSERT %s = %s;\n" % (self.save_variable(v0[0]), self.save_variable(v1[32 - s]))
        eqn += "ASSERT %s = %s;\n" % (self.save_variable(v0[s]), self.save_variable(v1[0]))
        self.__constraints.append(eqn)

    def R(self, fNa, isC, isF, isV, isK, s, in_var_v_m, in_var_d_m, in_var_v_a0, in_var_d_a0, in_var_v_a1,
          in_var_d_a1, in_var_v_a2, in_var_d_a2, in_var_v_a3, in_var_d_a3, in_var_v_a4, in_var_d_a4, in_var_v_a5,
          in_var_d_a5, in_var_a4, in_var_a3, in_var_a2, in_var_a5, in_var_a1, step):
        print("\n589: %s-R:" % step)
        """
        计算 a5 = a1⊞(F(a4, a3, a2)⊞ a0 ⊞ m ⊞ c)≪s 的轮函数
        :param fNa: 选择布尔函数，
        :param isC:控制布尔函数的具体选择，当siC=1，就选择boolfull-model模型
        :param isF:控制搜索策略1，搜索策略2;isF=1表示使用第一种搜索策略
        :param isV:当isV=1表示进一步检测矛盾点;
        :param isK:表示选择不同的扩展模型
        :param s:表示循环移位
        :param in_var_v_m:表示输入m的v
        :param in_var_d_m:表示输入m的d
        :param in_var_v_a0:表示输入a0的v
        :param in_var_d_a0:表示输入a0的d
        :param in_var_v_a1:表示输入a1的v
        :param in_var_d_a1:表示输入a1的d
        :param in_var_v_a2:表示输入a2的v
        :param in_var_d_a2:表示输入a2的d
        :param in_var_v_a3:表示输入a3的v
        :param in_var_d_a3:表示输入a3的d
        :param in_var_v_a4:表示输入a4的v
        :param in_var_d_a4:表示输入a4的d
        :param in_var_v_a5:表示输入a5的v
        :param in_var_d_a5:表示输入a5的d
        :param in_var_a4:表示输入a4的辅助变量
        :param in_var_a3:表示表示输入a3的辅助变量
        :param in_var_a2:表示输入a2的辅助变量
        :param in_var_a5:表示输入a5的辅助变量
        :param in_var_a1:表示输入a1的辅助变量
        :param step:表示步数
        :return:
        """
        # Claim signed difference vectors ∇b0,∇b1,∇b2,∇b3 of size 32,let a reputation b0, b1,b2,b3
        in_var_v_b0 = []
        in_var_d_b0 = []
        in_var_v_b1 = []
        in_var_d_b1 = []
        in_var_v_b2 = []
        in_var_d_b2 = []
        in_var_v_b3 = []
        in_var_d_b3 = []
        for i in range(32):
            in_var_v_b0.append("bv0" + "_" + str(step) + "_" + str(i))
            in_var_d_b0.append("bd0" + "_" + str(step) + "_" + str(i))
            in_var_v_b1.append("bv1" + "_" + str(step) + "_" + str(i))
            in_var_d_b1.append("bd1" + "_" + str(step) + "_" + str(i))
            in_var_v_b2.append("bv2" + "_" + str(step) + "_" + str(i))
            in_var_d_b2.append("bd2" + "_" + str(step) + "_" + str(i))
            in_var_v_b3.append("bv3" + "_" + str(step) + "_" + str(i))
            in_var_d_b3.append("bd3" + "_" + str(step) + "_" + str(i))

        # Claim signed difference vectors ∇c2,∇c3 of size 33.
        in_var_v_c2 = []
        in_var_d_c2 = []
        in_var_v_c3 = []
        in_var_d_c3 = []
        for i in range(33):
            in_var_v_c2.append("cv2" + "_" + str(step) + "_" + str(i))
            in_var_d_c2.append("cd2" + "_" + str(step) + "_" + str(i))
            in_var_v_c3.append("cv3" + "_" + str(step) + "_" + str(i))
            in_var_d_c3.append("cd3" + "_" + str(step) + "_" + str(i))
        # Claim a signed difference vector ∇q of size s + 1.
        in_var_v_q = []
        in_var_d_q = []
        for i in range(s + 1):
            in_var_v_q.append("qv" + "_" + str(step) + "_" + str(i))
            in_var_d_q.append("qd" + "_" + str(step) + "_" + str(i))
        # 将sigma-m赋值给中间变量b0
        eqn = "% assign m to b0\n"
        for i in range(32):
            eqn += "ASSERT %s = %s;\n" % (self.save_variable(in_var_v_m[i]), self.save_variable(in_var_v_b0[i]))
            eqn += "ASSERT %s = %s;\n" % (self.save_variable(in_var_d_m[i]), self.save_variable(in_var_d_b0[i]))
        self.__constraints.append(eqn)
        # print("722行代码表示将m赋值给b:\nASSERT %s\n"%eqn)
        self.boolfast_model(fNa, in_var_v_a4, in_var_d_a4, in_var_v_a3, in_var_d_a3, in_var_v_a2, in_var_d_a2,
                            in_var_v_b1, in_var_d_b1)
        if isC == 1:
            self.boolfull_model(fNa, in_var_v_a4, in_var_d_a4, in_var_v_a3, in_var_d_a3, in_var_v_a2,
                                in_var_d_a2, in_var_v_b1, in_var_d_b1, in_var_a4, in_var_a3, in_var_a2)
        # no carry for the least significant bit.
        eqn = "% no carry for the least significant bit 这部分是两个模加运算\n"
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable(in_var_v_c2[0]),
                                                             self.save_variable(in_var_d_c2[0]))
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable(in_var_v_c3[0]),
                                                             self.save_variable(in_var_d_c3[0]))
        self.__constraints.append(eqn)
        self.modadd_model(in_var_v_b0, in_var_d_b0, in_var_v_b1, in_var_d_b1, in_var_v_c2, in_var_d_c2,
                          in_var_v_b2, in_var_d_b2)
        self.modadd_model(in_var_v_b2, in_var_d_b2, in_var_v_a0, in_var_d_a0, in_var_v_c3, in_var_d_c3,
                          in_var_v_b3, in_var_d_b3)
        if isF == 1:
            self.rotate_diff_first(s, in_var_v_b3, in_var_d_b3, in_var_v_a1, in_var_d_a1, in_var_v_a5,
                                   in_var_d_a5, in_var_v_q, in_var_d_q, isV, isK, step)
        else:
            self.rotate_diff_second(s, in_var_v_b3, in_var_d_b3, in_var_v_a1, in_var_d_a1, in_var_v_a5,
                                    in_var_d_a5, in_var_v_q, in_var_d_q, isV, isK, step)
        if isV == 1:
            self.rotate_diff_filter(s, in_var_v_a5, in_var_d_a5, in_var_v_a1, in_var_d_a1, in_var_v_b3,
                                    in_var_d_b3, in_var_v_q, in_var_d_q, in_var_a5, in_var_a1, step)

    """检查赋值是否重复"""

    def check_assign(self, s):
        if s not in self.__assign:
            self.__assign.append(s)

    def assign_value(self):
        for i in range(self.__step - 5, self.__step):
            for j in range(32):
                temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable("xd_" + str(i) + "_" + str(j)),
                                                                     self.save_variable("xv_" + str(i) + "_" + str(j)))
                self.check_assign(temp)
        ss = [
            "==================u========u====",
            "=========================u======",
            "========u======================n",
            "====n===========================",
            "===n========================u===", ]
        for i in range(len(ss)):

            for j in range(32):
                if ss[i][j] == "=":
                    temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
                        self.save_variable("xd_" + str(i + 42) + "_" + str(31 - j)),
                        self.save_variable("xv_" + str(i + 42) + "_" + str(31 - j)))
                    self.check_assign(temp)
                elif ss[i][j] == "n":
                    temp = "ASSERT %s = 0bin1;\nASSERT %s = 0bin0;\n" % (
                        self.save_variable("xd_" + str(i + 42) + "_" + str(31 - j)),
                        self.save_variable("xv_" + str(i + 42) + "_" + str(31 - j)))
                    self.check_assign(temp)
                elif ss[i][j] == "u":
                    temp = "ASSERT %s = 0bin1;\nASSERT %s = 0bin1;\n" % (
                        self.save_variable("xd_" + str(i + 42) + "_" + str(31 - j)),
                        self.save_variable("xv_" + str(i + 42) + "_" + str(31 - j)))
                    self.check_assign(temp)
        obj = "ASSERT BVPLUS(10,"
        for j in range(32):
            if j == 31:
                obj += "0bin000000000@xd_%s_%s) = 0bin" % (41, j) + bin(3)[2:].zfill(10) + ";\n"
            else:
                obj += "0bin000000000@xd_%s_%s" % (41, j) + ", "
        self.check_assign(obj)
        obj = "ASSERT BVPLUS(10,"
        for j in range(32):
            if j == 31:
                obj += "0bin000000000@xd_%s_%s) = 0bin" % (40, j) + bin(3)[2:].zfill(10) + ";\n"
            else:
                obj += "0bin000000000@xd_%s_%s" % (40, j) + ", "
        self.check_assign(obj)
        obj = "ASSERT BVPLUS(10,"
        for j in range(32):
            if j == 31:
                obj += "0bin000000000@xd_%s_%s) = 0bin" % (39, j) + bin(4)[2:].zfill(10) + ";\n"
            else:
                obj += "0bin000000000@xd_%s_%s" % (39, j) + ", "
        self.check_assign(obj)
        obj = "ASSERT BVPLUS(10,"
        for j in range(32):
            if j == 31:
                obj += "0bin000000000@xd_%s_%s) = 0bin" % (38, j) + bin(6)[2:].zfill(10) + ";\n"
            else:
                obj += "0bin000000000@xd_%s_%s" % (38, j) + ", "
        self.check_assign(obj)
        obj = "ASSERT BVPLUS(10,"
        for j in range(32):
            if j == 31:
                obj += "0bin000000000@xd_%s_%s) = 0bin" % (37, j) + bin(6)[2:].zfill(10) + ";\n"
            else:
                obj += "0bin000000000@xd_%s_%s" % (37, j) + ", "
        self.check_assign(obj)
        obj = "ASSERT BVPLUS(10,"
        for j in range(32):
            if j == 31:
                obj += "0bin000000000@xd_%s_%s) = 0bin" % (36, j) + bin(6)[2:].zfill(10) + ";\n"
            else:
                obj += "0bin000000000@xd_%s_%s" % (36, j) + ", "
        self.check_assign(obj)
        obj = "ASSERT BVPLUS(10,"
        for j in range(32):
            if j == 31:
                obj += "0bin000000000@xd_%s_%s) = 0bin" % (35, j) + bin(3)[2:].zfill(10) + ";\n"
            else:
                obj += "0bin000000000@xd_%s_%s" % (35, j) + ", "
        self.check_assign(obj)

        obj = "ASSERT BVPLUS(10,"
        for i in range(17, 32):
            for j in range(32):
                if i == 31 and j == 31:
                    obj += "0bin000000000@xd_%s_%s) = 0bin" % (i, j) + bin(23)[2:].zfill(10) + ";\n"
                else:
                    obj += "0bin000000000@xd_%s_%s" % (i, j) + ", "
        self.check_assign(obj)

        for i in range(16):
            for j in range(32):
                if i == 12 and (j == 15):
                    temp = "ASSERT %s = 0bin1;\nASSERT %s = 0bin0;\n" % (
                        self.save_variable("md_" + str(i) + "_" + str(j)),
                        self.save_variable("mv_" + str(i) + "_" + str(j)))
                    self.check_assign(temp)

                else:
                    temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
                        self.save_variable("md_" + str(i) + "_" + str(j)),
                        self.save_variable("mv_" + str(i) + "_" + str(j)))
                    self.check_assign(temp)

    def Object(self, object_value):
        obj = "ASSERT BVPLUS(10,"
        for i in range(32, 35):
            for j in range(32):
                if i == 34 and j == 31:
                    obj += "0bin000000000@xd_%s_%s) = 0bin" % (i, j) + bin(object_value)[2:].zfill(10) + ";\n"
                else:
                    obj += "0bin000000000@xd_%s_%s" % (i, j) + ", "
        return obj

    def main(self):
        in_var_v_a = []
        in_var_d_a = []
        in_var_v_m = []
        in_var_d_m = []
        in_var_a = []
        for step in range(0, self.__bounds_rounds):
            temp_v_a = []
            temp_d_a = []
            temp_a = []
            for i in range(32):
                temp_v_a.append("xv_" + str(step) + "_" + str(i))
                temp_d_a.append("xd_" + str(step) + "_" + str(i))
                temp_a.append("x_" + str(step) + "_" + str(i))
            in_var_v_a.append(temp_v_a)
            in_var_d_a.append(temp_d_a)

            in_var_a.append(temp_a)
        for step in range(0, self.__bounds_rounds):
            temp_v_m = []
            temp_d_m = []
            for i in range(32):
                temp_v_m.append("mv_" + str(self.__OrderMessageWords_left[step]) + "_" + str(i))
                temp_d_m.append("md_" + str(self.__OrderMessageWords_left[step]) + "_" + str(i))
            in_var_v_m.append(temp_v_m)
            in_var_d_m.append(temp_d_m)

        for i in range(self.__step, self.__bounds_rounds):
            print((i - 5), self.__filterBool_left[(i - 5) // 16])
            self.R(self.__filterBool_left[(i - 5) // 16], self.__isc[i], self.__isf[i], self.__isv[i],
                   self.__isk[i],
                   self.__RotateCons_left[i],
                   in_var_v_m[i],
                   in_var_d_m[i],
                   self.left_shift(in_var_v_a[i - 5], 10),
                   self.left_shift(in_var_d_a[i - 5], 10),
                   self.left_shift(in_var_v_a[i - 4], 10),
                   self.left_shift(in_var_d_a[i - 4], 10),
                   self.left_shift(in_var_v_a[i - 3], 10),
                   self.left_shift(in_var_d_a[i - 3], 10),
                   in_var_v_a[i - 2],
                   in_var_d_a[i - 2],
                   in_var_v_a[i - 1],
                   in_var_d_a[i - 1],
                   in_var_v_a[i],
                   in_var_d_a[i],

                   in_var_a[i - 1],
                   in_var_a[i - 2],
                   self.left_shift(in_var_a[i - 3], 10),
                   in_var_a[i],
                   self.left_shift(in_var_a[i - 4], 10),
                   i)

    def solver(self):
        self.main()
        self.assign_value()
        constrain = "".join(self.__constraints)
        assign = "".join(self.__assign)
        variable = "".join(self.__declare)
        query = '\n' + 'QUERY FALSE;\nCOUNTEREXAMPLE;'

        for i in range(37, -1, -1):
            print("差分路线中有差分的个数为:%s" % i)
            obj = self.Object(i)
            file_write = open("left_model_40.cvc", "w")
            file_write.write(variable)
            file_write.write(constrain)
            file_write.write(assign)
            file_write.write(obj)
            file_write.write(query)
            file_write.close()
            stp_parameters = ["stp", "left_model_40.cvc", "--cryptominisat", "--threads", "16"]
            R = subprocess.check_output(stp_parameters)

            if "Valid.\n" != R.decode():
                file = open("right_res_0_9_" + str(i) + ".out", "w")
                print("差分路线中有差分的个数为:%s 满足" % i)
                file.write(R.decode())
                file.close()
            else:
                print("差分路线中有差分的个数为:%s 不满足" % i)
                break


if __name__ == '__main__':
    step = 17
    bounds = 47
    FunctionModel(step, bounds).solver()
