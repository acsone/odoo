# -*- coding: utf-8 -*-
# Part of Odoo. See LICENSE file for full copyright and licensing details.

from odoo import fields, models


class StockProductionLot(models.Model):
    _inherit = 'stock.production.lot'

    stock_valuation_layer_ids = fields.One2many(comodel_name='stock.valuation.layer', inverse_name='lot_id')
